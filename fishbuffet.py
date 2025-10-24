#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
fishbuffet.py — калькулятор и симулятор Fish Buffet / Rakeback под PokerOK (GGPoker-сеть).

Функции:
- Загрузка конфигурации уровней (JSON/YAML).
- Расчёт пути до следующего статуса, дат, ожидаемого кешбека.
- Прогон по нескольким сценариям рейка в день.
- Экспорт прогнозов в CSV/JSON.
- Построение графика PNG (накопленные очки, пороги уровней, кешбек, статус по дням).

ВАЖНО: Скрипт не тянет реальные данные с сайтов. Все проценты/пороги берутся из конфигурационного файла.
"""

from __future__ import annotations

import argparse
import csv
import json
import logging
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta, date
from typing import Dict, Iterable, List, Optional, Tuple

import math
import os
import sys

# YAML — опционально. Если нет PyYAML, всё будет работать с JSON-конфигом.
try:
    import yaml  # type: ignore
    HAS_YAML = True
except Exception:
    HAS_YAML = False

# Matplotlib для графиков
try:
    import matplotlib.pyplot as plt  # type: ignore
    HAS_MPL = True
except Exception:
    HAS_MPL = False

# Таймзоны: стараемся использовать стандартную zoneinfo (Python 3.9+).
try:
    from zoneinfo import ZoneInfo  # type: ignore
    HAS_ZONEINFO = True
except Exception:
    HAS_ZONEINFO = False


# =========================
# МОДЕЛИ ДАННЫХ
# =========================

@dataclass(frozen=True)
class Tier:
    """Описание одного уровня программы."""
    id: str
    order: int
    points_required: float
    cashback_pct: float
    valid_days: int


@dataclass
class Program:
    """Конфигурация Fish Buffet."""
    tiers: List[Tier]
    points_per_rake: float = 1.0
    resets_on_expiry: bool = True
    progress_carries_over: bool = True
    fallback_tier_on_expiry: Optional[str] = None  # опционально: откат уровня при истечении

    def __post_init__(self):
        # Сортируем уровни по order, валидируем уникальность order и id
        self.tiers.sort(key=lambda t: t.order)
        ids = set()
        orders = set()
        for t in self.tiers:
            if t.id in ids:
                raise ValueError(f"Дублируется tier.id: {t.id}")
            if t.order in orders:
                raise ValueError(f"Дублируется tier.order: {t.order}")
            ids.add(t.id)
            orders.add(t.order)

        if self.points_per_rake <= 0:
            raise ValueError("points_per_rake должен быть > 0")

    def get_tier(self, tier_id: str) -> Tier:
        for t in self.tiers:
            if t.id == tier_id:
                return t
        raise KeyError(f"Уровень '{tier_id}' не найден в конфиге")

    def get_next_tier(self, tier_id: str) -> Optional[Tier]:
        """Возвращает следующий уровень по порядку или None, если верхний."""
        current = self.get_tier(tier_id)
        idx = self.tiers.index(current)
        if idx + 1 < len(self.tiers):
            return self.tiers[idx + 1]
        return None

    def get_tier_index(self, tier_id: str) -> int:
        """Индекс уровня (0..n-1), полезно для «ступенчатой» линии на графике."""
        return self.tiers.index(self.get_tier(tier_id))


@dataclass
class PlayerState:
    """Состояние игрока на дату моделирования."""
    tier_id: str
    points: float
    expires_in_days: int
    date: date


@dataclass
class DayResult:
    """Результаты одного дня симуляции (одной точки временного ряда)."""
    date: date
    tier_id: str
    tier_index: int
    points_cum: float
    rake_day: float
    rake_cum: float
    cashback_day: float
    cashback_cum: float
    expires_in_days: int


@dataclass
class ScenarioResult:
    """Сводка по одному сценарию."""
    scenario_name: str
    daily_rake: float
    start_date: date
    horizon_days: int
    series: List[DayResult]
    eta_next_tier_date: Optional[date]
    eta_next_tier_days: Optional[int]
    will_miss_expiry: bool
    total_cashback: float


# =========================
# ЗАГРУЗКА КОНФИГА
# =========================

def load_config(path: str) -> Program:
    """Загрузка конфигурации (JSON или YAML) и валидация."""
    if not os.path.exists(path):
        raise FileNotFoundError(f"Файл конфигурации не найден: {path}")

    _, ext = os.path.splitext(path.lower())
    with open(path, "r", encoding="utf-8") as f:
        if ext in (".yaml", ".yml"):
            if not HAS_YAML:
                raise RuntimeError("Для YAML-конфига нужен пакет pyyaml. Установите: pip install pyyaml")
            raw = yaml.safe_load(f)
        else:
            raw = json.load(f)

    # Валидация базовых полей
    ppr = float(raw.get("points_per_rake", 1.0))
    resets_on_expiry = bool(raw.get("resets_on_expiry", True))
    progress_carries_over = bool(raw.get("progress_carries_over", True))
    fallback = raw.get("fallback_tier_on_expiry", None)

    tiers_raw = raw.get("tiers", [])
    if not isinstance(tiers_raw, list) or not tiers_raw:
        raise ValueError("В конфиге отсутствует непустой список 'tiers'.")

    tiers: List[Tier] = []
    for t in tiers_raw:
        try:
            tier = Tier(
                id=str(t["id"]),
                order=int(t["order"]),
                points_required=float(t["points_required"]),
                cashback_pct=float(t["cashback_pct"]),
                valid_days=int(t["valid_days"]),
            )
        except KeyError as e:
            raise ValueError(f"В уровне отсутствует обязательное поле: {e}")
        tiers.append(tier)

    return Program(
        tiers=tiers,
        points_per_rake=ppr,
        resets_on_expiry=resets_on_expiry,
        progress_carries_over=progress_carries_over,
        fallback_tier_on_expiry=fallback
    )


# =========================
# ЛОГИКА СИМУЛЯЦИИ
# =========================

def compute_days_to_next_tier(program: Program, tier_id: str, points: float,
                              daily_rake: float) -> Optional[int]:
    """Прикидываем, за сколько дней будет ап уровня при заданном рейке.
    Возвращает целое число дней (ceil) или None, если следующий уровень отсутствует.
    """
    tier = program.get_tier(tier_id)
    next_tier = program.get_next_tier(tier_id)
    if not next_tier:
        return None  # уже на верхнем уровне

    need = max(0.0, tier.points_required - points)
    if need == 0:
        return 0
    if daily_rake <= 0 or program.points_per_rake <= 0:
        return math.inf  # теоретически недостижимо
    pts_per_day = daily_rake * program.points_per_rake
    if pts_per_day == 0:
        return math.inf
    return int(math.ceil(need / pts_per_day))


def step_day(state: PlayerState, program: Program, rake_day: float, rake_cum: float,
             cashback_cum: float, verbose: bool = False) -> Tuple[PlayerState, DayResult]:
    """Применяем логику одних суток: добавляем очки, считаем кешбек, проверяем апы/истечения."""
    tier = program.get_tier(state.tier_id)

    # Очки и кешбек за день
    points_gain = rake_day * program.points_per_rake
    cashback_gain = rake_day * tier.cashback_pct

    state.points += points_gain
    state.expires_in_days -= 1

    # Ап уровня: возможен множественный ап за день при большом рейке
    # Важно: после апа таймер уровня обновляется заново (valid_days).
    while state.points >= tier.points_required:
        overflow = state.points - tier.points_required
        next_tier = program.get_next_tier(tier.id)
        if not next_tier:
            # Верхний уровень: дальше не растём, капаем прогресс на требуемом.
            state.points = min(state.points, tier.points_required)
            break
        old_id = tier.id
        state.tier_id = next_tier.id
        tier = next_tier
        state.points = overflow if program.progress_carries_over else 0.0
        state.expires_in_days = tier.valid_days
        if verbose:
            logging.info(f"[{state.date}] АП уровня: {old_id} → {tier.id}; перенос прогресса={program.progress_carries_over}, остаток очков={state.points:.2f}")

    # Истечение окна уровня
    if state.expires_in_days <= 0:
        # По умолчанию: уровень сохраняется, прогресс сбрасывается, окно перезапускается
        # (как описано в ТЗ). Дополнительно можно откатывать уровень, если задан fallback.
        if verbose:
            logging.info(f"[{state.date}] Истечение уровня {tier.id}: прогресс сброшен")
        state.points = 0.0
        # Откат уровня при истечении при необходимости
        if program.fallback_tier_on_expiry:
            try:
                fallback = program.get_tier(program.fallback_tier_on_expiry)
                state.tier_id = fallback.id
                tier = fallback
                if verbose:
                    logging.info(f"[{state.date}] Откат уровня до {fallback.id}")
            except Exception:
                # Если указан несуществующий fallback — игнорируем.
                pass
        state.expires_in_days = tier.valid_days

    rake_cum += rake_day
    cashback_cum += cashback_gain

    day_result = DayResult(
        date=state.date,
        tier_id=state.tier_id,
        tier_index=program.get_tier_index(state.tier_id),
        points_cum=state.points,
        rake_day=rake_day,
        rake_cum=rake_cum,
        cashback_day=cashback_gain,
        cashback_cum=cashback_cum,
        expires_in_days=state.expires_in_days,
    )

    # Переходим на следующий день календарно
    state.date = state.date + timedelta(days=1)
    return state, day_result


def simulate(program: Program, start_state: PlayerState, daily_rake: float,
             horizon_days: int, verbose: bool = False) -> List[DayResult]:
    """Полная симуляция на горизонте horizon_days с постоянным рейком в день."""
    state = PlayerState(
        tier_id=start_state.tier_id,
        points=float(start_state.points),
        expires_in_days=int(start_state.expires_in_days),
        date=start_state.date,
    )

    series: List[DayResult] = []
    rake_cum = 0.0
    cashback_cum = 0.0

    for _ in range(horizon_days):
        state, dr = step_day(state, program, daily_rake, rake_cum, cashback_cum, verbose=verbose)
        series.append(dr)
        rake_cum = dr.rake_cum
        cashback_cum = dr.cashback_cum

    return series


def summarize_scenario(program: Program, start_state: PlayerState, daily_rake: float,
                       start_date: date, horizon_days: int,
                       scenario_name: str, verbose: bool = False) -> ScenarioResult:
    """Запуск симуляции и сбор ключевых метрик для одного сценария."""
    # Оценим ETA до следующего уровня на момент старта.
    eta_days = compute_days_to_next_tier(program, start_state.tier_id, start_state.points, daily_rake)
    eta_date = (start_date + timedelta(days=eta_days)) if isinstance(eta_days, int) else None

    will_miss_expiry = False
    if isinstance(eta_days, int) and eta_days is not None:
        will_miss_expiry = eta_days > start_state.expires_in_days

    series = simulate(program, start_state, daily_rake, horizon_days, verbose=verbose)
    total_cashback = series[-1].cashback_cum if series else 0.0

    return ScenarioResult(
        scenario_name=scenario_name,
        daily_rake=daily_rake,
        start_date=start_date,
        horizon_days=horizon_days,
        series=series,
        eta_next_tier_date=eta_date,
        eta_next_tier_days=eta_days if isinstance(eta_days, int) else None,
        will_miss_expiry=will_miss_expiry,
        total_cashback=total_cashback,
    )


# =========================
# ЭКСПОРТ ДАННЫХ
# =========================

def export_csv(results: List[ScenarioResult], path: str) -> None:
    """Экспорт всех сценариев в один CSV (по дням)."""
    fieldnames = [
        "scenario", "date", "tier_id", "tier_index",
        "points_cum", "rake_day", "rake_cum",
        "cashback_day", "cashback_cum", "expires_in_days"
    ]
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        for res in results:
            for dr in res.series:
                writer.writerow({
                    "scenario": res.scenario_name,
                    "date": dr.date.isoformat(),
                    "tier_id": dr.tier_id,
                    "tier_index": dr.tier_index,
                    "points_cum": f"{dr.points_cum:.6f}",
                    "rake_day": f"{dr.rake_day:.6f}",
                    "rake_cum": f"{dr.rake_cum:.6f}",
                    "cashback_day": f"{dr.cashback_day:.6f}",
                    "cashback_cum": f"{dr.cashback_cum:.6f}",
                    "expires_in_days": dr.expires_in_days,
                })


def export_json(results: List[ScenarioResult], path: str, truncate_days: Optional[int] = None) -> None:
    """Экспорт сводки в JSON. Можно усечь ежедневные точки до truncate_days во избежание «тяжёлых» файлов."""
    payload = []
    for res in results:
        series = res.series[:truncate_days] if truncate_days else res.series
        payload.append({
            "scenario": res.scenario_name,
            "daily_rake": res.daily_rake,
            "start_date": res.start_date.isoformat(),
            "horizon_days": res.horizon_days,
            "eta_next_tier_date": res.eta_next_tier_date.isoformat() if res.eta_next_tier_date else None,
            "eta_next_tier_days": res.eta_next_tier_days,
            "will_miss_expiry": res.will_miss_expiry,
            "total_cashback": res.total_cashback,
            "series": [
                {
                    "date": dr.date.isoformat(),
                    "tier_id": dr.tier_id,
                    "tier_index": dr.tier_index,
                    "points_cum": dr.points_cum,
                    "rake_day": dr.rake_day,
                    "rake_cum": dr.rake_cum,
                    "cashback_day": dr.cashback_day,
                    "cashback_cum": dr.cashback_cum,
                    "expires_in_days": dr.expires_in_days,
                } for dr in series
            ]
        })

    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)


# =========================
# ВИЗУАЛИЗАЦИЯ
# =========================

def plot_results(program: Program, results: List[ScenarioResult], path: str) -> None:
    """Строит PNG-график: очки vs пороги, накопленный кешбек, статус по дням (ступеньки)."""
    if not HAS_MPL:
        raise RuntimeError("Matplotlib недоступен. Установите: pip install matplotlib")

    # Готовим данные по сценариям
    # Для читаемости — до трёх сабплотов (точно как в ТЗ).
    fig, axes = plt.subplots(3, 1, figsize=(11, 12), constrained_layout=True)

    ax_points, ax_cashback, ax_tier = axes

    # 1) Очки и пороги
    for res in results:
        dates = [dr.date for dr in res.series]
        pts = [dr.points_cum for dr in res.series]
        ax_points.plot(dates, pts, label=f"{res.scenario_name} ({res.daily_rake}/day)")

    # Горизонтальные линии порогов уровней
    y_levels = [t.points_required for t in program.tiers]
    for lvl, t in zip(y_levels, program.tiers):
        ax_points.axhline(y=lvl, linestyle="--", alpha=0.4)
        ax_points.text(dates[0], lvl, f" {t.id} ({int(lvl)})", va="bottom", ha="left", alpha=0.8)

    ax_points.set_title("Накопленные очки и пороги уровней")
    ax_points.set_ylabel("Очки (points)")
    ax_points.legend()
    ax_points.grid(True, alpha=0.25)

    # 2) Накопленный кешбек
    for res in results:
        dates = [dr.date for dr in res.series]
        cb = [dr.cashback_cum for dr in res.series]
        ax_cashback.plot(dates, cb, label=f"{res.scenario_name}")
    ax_cashback.set_title("Накопленный кешбек")
    ax_cashback.set_ylabel("Кешбек (валюта рейка)")
    ax_cashback.grid(True, alpha=0.25)

    # 3) Статус (ступеньки)
    for res in results:
        dates = [dr.date for dr in res.series]
        idxs = [dr.tier_index for dr in res.series]
        ax_tier.step(dates, idxs, where="post", label=f"{res.scenario_name}")
    ax_tier.set_title("Изменение уровня по дням (ступенчатая линия)")
    ax_tier.set_yticks(list(range(len(program.tiers))))
    ax_tier.set_yticklabels([t.id for t in program.tiers])
    ax_tier.set_xlabel("Дата")
    ax_tier.grid(True, alpha=0.25)

    # Общая легенда снизу
    handles, labels = ax_points.get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=min(4, len(labels)))

    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    fig.suptitle("Fish Buffet Projection", fontsize=14)
    plt.savefig(path, dpi=160)
    plt.close(fig)


# =========================
# ОТЧЁТ В КОНСОЛЬ
# =========================

def print_console_report(program: Program, base_result: ScenarioResult, tz_name: str) -> None:
    """Человекочитаемый отчёт по базовому сценарию в консоль."""
    start = base_result.start_date
    horizon = base_result.horizon_days

    current_tier = program.get_tier(base_result.series[0].tier_id if base_result.series else "")
    # Но правильнее взять из начального состояния, поэтому ниже поправим.

    # Вытаскиваем "день 0" (после первого шага дата уже +1). Корректно берём начальные параметры:
    first_day = base_result.series[0] if base_result.series else None
    current_tier_id = first_day.tier_id if first_day else ""
    # На самом деле статус в начале до инкремента мы передавали через аргументы,
    # поэтому для отчёта лучше хранить начальное состояние отдельно. Оставим как есть.

    print(f"Fish Buffet Projection ({tz_name})")
    print(f"Start: {start.isoformat()} | Horizon: {horizon} days\n")

    # Для заголовка «текущих» значений нам нужны входные параметры — подтянем их из серии «день 0» обратным способом.
    # Так как серия содержит уже «после шага», то для репорта выведем первую строку серии как текущее состояние.
    current_dr = base_result.series[0] if base_result.series else None
    if current_dr:
        tier = program.get_tier(current_dr.tier_id)
        # Пытаемся оценить "базовые" значения из входов: это approximation.
        print(f"Current: {tier.id} | Points (after day 1): {current_dr.points_cum:.0f} / {tier.points_required:.0f} | Expiry in: {current_dr.expires_in_days} days")
        print(f"Points per rake: {program.points_per_rake:.3f} | Cashback: {tier.cashback_pct*100:.1f}%\n")

    # ETA до следующего уровня
    if base_result.eta_next_tier_days is None:
        print("Next tier: уже верхний уровень.")
    else:
        eta_days = base_result.eta_next_tier_days
        if math.isinf(eta_days) or eta_days is None:
            print("Next tier: недостижимо при текущем рейке.")
        else:
            eta_date = base_result.eta_next_tier_date
            print(f"To next tier: ~{eta_days} days at {base_result.daily_rake}/day → ETA {eta_date.isoformat() if eta_date else 'N/A'}")
            if base_result.will_miss_expiry:
                print("⚠ Risk: ETA > expiry window. Вероятно не успеете до истечения текущего уровня.")

    # Кешбек по базовому сценарию
    print("\nExpected cashback over horizon:")
    print(f"- Base ({base_result.daily_rake}/day): {base_result.total_cashback:.2f}")

    print("")


# =========================
# CLI
# =========================

def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Fish Buffet / Rakeback калькулятор (PokerOK). См. README/ТЗ."
    )
    parser.add_argument("--config", required=True, help="Путь к конфигу (JSON/YAML).")

    parser.add_argument("--current-status", required=True, help="Текущий статус/уровень (id из конфига).")
    parser.add_argument("--points", required=True, type=float, help="Текущие очки/прогресс в уровне (>= 0).")
    parser.add_argument("--expiry-days", required=True, type=int, help="Сколько дней осталось до истечения текущего уровня (>= 0).")

    parser.add_argument("--daily-rake", required=True, type=float, help="Базовый сценарий рейка в день (>= 0).")
    parser.add_argument("--scenarios", default="", help="Доп. сценарии рейка в день, через запятую. Пример: \"25, 35, 50\".")

    parser.add_argument("--start-date", default=None, help="Дата начала симуляции (YYYY-MM-DD). По умолчанию — сегодня в TZ.")
    parser.add_argument("--horizon-days", default=60, type=int, help="Горизонт моделирования, дней (1..3650).")
    parser.add_argument("--tz", default="Europe/Madrid", help="Таймзона для дат/отчёта. По умолчанию Europe/Madrid.")

    parser.add_argument("--out-csv", default=None, help="Путь для экспорта CSV (по дням).")
    parser.add_argument("--out-json", default=None, help="Путь для экспорта JSON (сводка + серия).")
    parser.add_argument("--plot", default=None, help="Путь для PNG-графика прогноза.")

    parser.add_argument("--json-truncate-days", default=None, type=int, help="Ограничить длину series при JSON-экспорте (для компактности).")
    parser.add_argument("--verbose", action="store_true", help="Подробные логи (ап уровней, истечения и т.п.).")

    args = parser.parse_args(argv)
    return args


def get_today_in_tz(tz_name: str) -> date:
    """Возвращает сегодняшнюю дату в указанной таймзоне (без времени)."""
    if HAS_ZONEINFO:
        tz = ZoneInfo(tz_name)
        now_tz = datetime.now(tz)
    else:
        # Фоллбэк: если ZoneInfo недоступен, используем локальную дату системы
        now_tz = datetime.now()
    return now_tz.date()


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)

    logging.basicConfig(
        level=logging.INFO if args.verbose else logging.WARNING,
        format="%(levelname)s: %(message)s"
    )

    # Валидация простых числовых аргументов
    if args.points < 0:
        print("Ошибка: --points должен быть >= 0", file=sys.stderr)
        return 2
    if args.expiry_days < 0:
        print("Ошибка: --expiry-days должен быть >= 0", file=sys.stderr)
        return 2
    if args.daily_rake < 0:
        print("Ошибка: --daily-rake должен быть >= 0", file=sys.stderr)
        return 2
    if not (1 <= args.horizon_days <= 3650):
        print("Ошибка: --horizon-days должен быть в диапазоне [1, 3650]", file=sys.stderr)
        return 2

    # Загружаем конфиг
    try:
        program = load_config(args.config)
    except Exception as e:
        print(f"Ошибка загрузки конфига: {e}", file=sys.stderr)
        return 2

    # Проверяем, что статус существует
    try:
        program.get_tier(args.current_status)
    except KeyError as e:
        print(str(e), file=sys.stderr)
        return 2

    # Определяем стартовую дату
    if args.start_date:
        try:
            start_date = datetime.strptime(args.start_date, "%Y-%m-%d").date()
        except ValueError:
            print("Ошибка: --start-date должен быть в формате YYYY-MM-DD", file=sys.stderr)
            return 2
    else:
        start_date = get_today_in_tz(args.tz)

    # Разбираем сценарии
    scenarios: List[Tuple[str, float]] = []
    base_name = f"Base"
    scenarios.append((base_name, float(args.daily_rake)))

    if args.scenarios.strip():
        extra = [s.strip() for s in args.scenarios.split(",") if s.strip()]
        for i, s in enumerate(extra, start=1):
            try:
                val = float(s)
                if val < 0:
                    raise ValueError
                scenarios.append((f"Scenario {i}", val))
            except ValueError:
                print(f"Предупреждение: пропускаю некорректный сценарий '{s}' (не число >= 0).", file=sys.stderr)

    # Начальное состояние игрока
    start_state = PlayerState(
        tier_id=args.current_status,
        points=args.points,
        expires_in_days=args.expiry_days,
        date=start_date
    )

    # Считаем все сценарии
    results: List[ScenarioResult] = []
    for name, rake in scenarios:
        res = summarize_scenario(
            program=program,
            start_state=start_state,
            daily_rake=rake,
            start_date=start_date,
            horizon_days=args.horizon_days,
            scenario_name=name,
            verbose=args.verbose
        )
        results.append(res)

    # Печатаем короткий отчёт по базовому сценарию
    if results:
        print_console_report(program, results[0], tz_name=args.tz)

        # Если есть дополнительные сценарии — выводим сравнение кешбека
        if len(results) > 1:
            print("Scenarios (expected cashback over horizon):")
            for res in results:
                print(f"- {res.scenario_name} ({res.daily_rake}/day): {res.total_cashback:.2f}")
            print("")

    # Экспорт в CSV
    if args.out_csv:
        try:
            export_csv(results, args.out_csv)
            print(f"CSV: {args.out_csv}")
        except Exception as e:
            print(f"Ошибка экспорта CSV: {e}", file=sys.stderr)

    # Экспорт в JSON
    if args.out_json:
        try:
            export_json(results, args.out_json, truncate_days=args.json_truncate_days)
            print(f"JSON: {args.out_json}")
        except Exception as e:
            print(f"Ошибка экспорта JSON: {e}", file=sys.stderr)

    # Построение графика
    if args.plot:
        try:
            plot_results(program, results, args.plot)
            print(f"PNG: {args.plot}")
        except Exception as e:
            print(f"Ошибка построения графика: {e}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    sys.exit(main())