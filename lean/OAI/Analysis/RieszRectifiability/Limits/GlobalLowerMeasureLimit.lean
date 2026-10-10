import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitLowerMass
import OAI.Analysis.RieszRectifiability.Limits.CompactLimitOrigin
import OAI.Analysis.RieszRectifiability.Limits.OriginalGrowthLimit

namespace OAI

/-!
# Global lower growth in measure limits

Compact-test convergence transfers lower ball-mass bounds to support points of the
limit, with the explicit factor `4 ^ n`. Combined with global upper growth and an origin
normalization, this produces a nonzero subsequential limit with both growth estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem compactTestConvergence_global_lower {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hC : 0 < C)
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r)) :
    ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  intro x hx r hr
  have hquarter : 0 < r / 4 := by positivity
  have heq : (r / 4) ^ n / C = r ^ n / (C * 4 ^ n) := by
    rw [div_pow]
    ring
  have hbound : ∀ᶠ j in atTop, ∀ y ∈ (μ j).support,
      r ^ n / (C * 4 ^ n) ≤ (μ j).real (ball y (r / 4)) := by
    apply Filter.Eventually.of_forall
    intro j y hy
    have hfinite : (μ j) (ball y (r / 4)) ≠ ∞ :=
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall y (r / 4)).measure_lt_top).ne
    have h := ENNReal.toReal_mono hfinite (hlower j y hy (r / 4) hquarter)
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r / 4) ^ n / C)] at h
    simpa only [heq, Measure.real] using! h
  have hreal := compactTestConvergence_lower_ball_mass μ ν hlocal x hx r _ hr hbound
  calc
    _ ≤ ENNReal.ofReal (ν.real (ball x r)) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := ENNReal.ofReal_toReal
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall x r).measure_lt_top).ne

theorem exists_global_growth_measure_limit {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasureOnCompacts (μ j)]
    (C G : ℝ) (hC : 0 < C) (hg : ∀ j, GlobalUpperGrowth n G (μ j))
    (hlower : ∀ j x, x ∈ (μ j).support → ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (r ^ n / C) ≤ (μ j) (ball x r))
    (hzero : ∀ j, (0 : Ambient d) ∈ (μ j).support) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ ν : Measure (Ambient d),
      IsFiniteMeasureOnCompacts ν ∧ ν ≠ 0 ∧
      CompactTestConvergence (fun j => μ (ρ j)) ν ∧ GlobalUpperGrowth n (G * 2 ^ n) ν ∧
      (0 : Ambient d) ∈ ν.support ∧
      ∀ x ∈ ν.support, ∀ r : ℝ, 0 < r →
        ENNReal.ofReal (r ^ n / (C * 4 ^ n)) ≤ ν (ball x r) := by
  have hmass : ∀ j, C⁻¹ ≤ (μ j).real (ball (0 : Ambient d) 1) := by
    intro j
    have h := ENNReal.toReal_mono
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) 1).measure_lt_top).ne
      (hlower j 0 (hzero j) 1 zero_lt_one)
    simpa only [one_pow, one_div, ENNReal.toReal_ofReal (inv_nonneg.mpr hC.le), Measure.real] using! h
  obtain ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν⟩ :=
    exists_original_growth_limit n μ G C⁻¹ (inv_pos.mpr hC) hg hmass
  let := hfinite
  have horigin : (0 : Ambient d) ∈ ν.support := by
    apply compactTestConvergence_mem_support_of_ball_masses (fun j => μ (ρ j)) ν hlocal 0
    intro r hr
    refine ⟨r ^ n / C, by positivity, Filter.Eventually.of_forall fun j => ?_⟩
    have h := ENNReal.toReal_mono
      ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : Ambient d) r).measure_lt_top).ne
      (hlower (ρ j) 0 (hzero (ρ j)) r hr)
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ n / C), Measure.real] using! h
  exact ⟨ρ, hρ, ν, hfinite, hne, hlocal, hgν, horigin,
    compactTestConvergence_global_lower n (fun j => μ (ρ j)) ν hlocal C hC
      (fun j => hlower (ρ j))⟩

end

end RieszRectifiability

end OAI
