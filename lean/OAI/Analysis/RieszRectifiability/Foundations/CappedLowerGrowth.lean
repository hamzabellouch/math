import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BlowupMeasure
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitLowerMass
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitOrigin

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def CappedLowerGrowth {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d)) : Prop :=
  ∀ x ∈ μ.support, ∀ r : ℝ, 0 < r → r ≤ H → ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)

theorem CappedLowerGrowth.real_bound {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasureOnCompacts μ]
    (hC : 0 < C) (hlower : CappedLowerGrowth n C H μ)
    (x : Ambient d) (hx : x ∈ μ.support) (r : ℝ) (hr : 0 < r) (hrH : r ≤ H) :
    r ^ n / C ≤ μ.real (ball x r) := by
  have hfinite : μ (ball x r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne
  have h := ENNReal.toReal_mono hfinite (hlower x hx r hr hrH)
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ n / C)] using! h

theorem CappedLowerGrowth.blowup {d : ℕ} (n : ℕ) (C H : ℝ) (μ : Measure (Ambient d))
    (hlower : CappedLowerGrowth n C H μ) (a : Ambient d) (s : ℝ) (hs : 0 < s) :
    CappedLowerGrowth n C (H / s) (blowupMeasure n μ a s) := by
  intro x hx R hR hRH
  rw [blowupMeasure_ball n μ a x s R hs]
  have hscaled : s * R ≤ H := by
    have h := (le_div_iff₀ hs).mp hRH
    simpa only [mul_comm] using! h
  have hl := hlower (a + s • x) ((blowupMeasure_support_iff n μ a x s hs).mp hx)
    (s * R) (mul_pos hs hR) hscaled
  calc
    _ = ENNReal.ofReal ((s ^ n)⁻¹) * ENNReal.ofReal ((s * R) ^ n / C) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (s ^ n)⁻¹)]
      congr 1
      rw [mul_pow]
      field_simp
    _ ≤ _ := mul_le_mul_right hl _

theorem CappedLowerGrowth.compact_limit {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hlocal : CompactTestConvergence μ ν)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) : CappedLowerGrowth n (C * 4 ^ n) H ν := by
  intro x hx r hr hrH
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by rw [div_pow]; ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    apply Eventually.of_forall
    intro j y hy
    rw [← heq]
    exact CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) y hy (r / 4)
      (by positivity) (by linarith)
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

theorem CappedLowerGrowth.limit_origin {d : ℕ} (n : ℕ) (C H : ℝ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hC : 0 < C) (hH : 0 < H) (hlocal : CompactTestConvergence μ ν)
    (hlower : ∀ j, CappedLowerGrowth n C H (μ j)) (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    (0 : Ambient d) ∈ ν.support := by
  apply compactTestConvergence_mem_support_of_ball_masses μ ν hlocal 0
  intro r hr
  let t := min r H
  have ht : 0 < t := lt_min hr hH
  refine ⟨t ^ n / C, by positivity, Eventually.of_forall fun j => ?_⟩
  have hl := CappedLowerGrowth.real_bound n C H (μ j) hC (hlower j) 0 (hzero j) t ht (min_le_right _ _)
  apply hl.trans
  exact ENNReal.toReal_mono
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) r).measure_lt_top).ne
    (measure_mono (ball_subset_ball (min_le_left r H)))

end

end RieszRectifiability

end OAI
