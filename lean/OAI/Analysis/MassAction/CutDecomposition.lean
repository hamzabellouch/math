import Mathlib

namespace OAI

universe uE

/-! The weighted level difference is the integral of the flux over all
threshold cuts. This avoids choosing an ordering of the distinct levels. -/

namespace Problem326.CutFlux

open scoped BigOperators
open MeasureTheory

private theorem integrable_interval_indicator (a b q : ℝ) :
    Integrable ((Set.Ico a b).indicator (fun _ : ℝ => q)) := by
  apply (integrable_indicator_iff measurableSet_Ico).2
  exact integrableOn_const (by simp)

private theorem integral_signed_interval (a b q : ℝ) :
    (∫ c : ℝ, ((Set.Ico a b).indicator (fun _ : ℝ => q) c -
      (Set.Ico b a).indicator (fun _ : ℝ => q) c)) = q * (b - a) := by
  rw [integral_sub (integrable_interval_indicator a b q)
    (integrable_interval_indicator b a q)]
  simp only [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico, smul_eq_mul]
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring

/-- If every threshold cut has nonnegative net flux, then the weighted sum
of level differences is nonnegative. Edge weights can have either sign. -/
theorem weighted_difference_nonneg_of_threshold_flux {E : Type uE} [Fintype E]
    (s t q : E → ℝ)
    (hcut : ∀ c : ℝ,
      0 ≤ (∑ e ∈ Finset.univ.filter (fun e => s e ≤ c ∧ c < t e), q e) -
          (∑ e ∈ Finset.univ.filter (fun e => t e ≤ c ∧ c < s e), q e)) :
    0 ≤ ∑ e, q e * (t e - s e) := by
  classical
  let f : E → ℝ → ℝ := fun e c =>
    (Set.Ico (s e) (t e)).indicator (fun _ : ℝ => q e) c -
    (Set.Ico (t e) (s e)).indicator (fun _ : ℝ => q e) c
  have hf : ∀ e, Integrable (f e) := fun e =>
    (integrable_interval_indicator (s e) (t e) (q e)).sub
      (integrable_interval_indicator (t e) (s e) (q e))
  have hnonneg : ∀ c, 0 ≤ ∑ e, f e c := by
    intro c
    simpa only [f, Finset.sum_sub_distrib, Set.indicator_apply, Set.mem_Ico,
      Finset.sum_filter] using hcut c
  have hint : 0 ≤ ∫ c : ℝ, ∑ e, f e c := integral_nonneg (fun c => hnonneg c)
  rw [integral_finsetSum Finset.univ (fun e _ => hf e)] at hint
  simpa only [f, integral_signed_interval] using hint

end Problem326.CutFlux

end OAI
