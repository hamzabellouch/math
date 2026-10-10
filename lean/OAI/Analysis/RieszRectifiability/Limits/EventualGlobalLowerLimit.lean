import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitLowerMass
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitOrigin

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem compactTestConvergence_eventual_global_lower {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hlocal : CompactTestConvergence μ ν)
    (hlower : ∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, ∀ x ∈ (μ j).support,
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r)) :
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r → ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  intro x hx r hr
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by rw [div_pow]; ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    filter_upwards [hlower (r / 4) (by positivity)] with j hj
    intro y hy
    have hfinite : (μ j) (ball y (r / 4)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y (r / 4)).measure_lt_top).ne
    have h := ENNReal.toReal_mono hfinite (hj y hy)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C), heq] at h
    exact h
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

end

end RieszRectifiability

end OAI
