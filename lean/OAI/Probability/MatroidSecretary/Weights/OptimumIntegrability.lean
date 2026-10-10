import OAI.Probability.MatroidSecretary.Weights.DegenerateCases
import OAI.Probability.MatroidProphet.Main
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-!
# The exact finite-moment requirement

For a finite matroid and nonnegative measurable weights, integrability of the
actual offline optimum is equivalent to integrability of the nonloop
coordinates. No loop-coordinate moments are imposed. This is a supporting
scope check for introduction.tex, Theorem `thm:main`, and setup.tex's
one-sample simulation argument; it does not replace its competitive claim.
-/

namespace MatroidProphet.DegenerateCases

open MeasureTheory Classical
open scoped BigOperators

/-- Only nonloops can contribute to a feasible sum. -/
theorem optimum_le_sum_nonloops {n : ℕ} (M : Matroid (Fin n))
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    optimum M w ≤ ∑ e : Fin n, if M.IsNonloop e then w e else 0 := by
  classical
  have hn (e : Fin n) : 0 ≤ if M.IsNonloop e then w e else 0 := by
    split_ifs
    · exact hw e
    · exact le_rfl
  apply optimum_le_of_independent_bound M w _ (Finset.sum_nonneg fun e _ => hn e)
  intro I hI
  calc
    (∑ e ∈ I, w e) = ∑ e ∈ I, if M.IsNonloop e then w e else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      simp [hI.isNonloop_of_mem he]
    _ ≤ ∑ e : Fin n, if M.IsNonloop e then w e else 0 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
        (fun e _ _ => hn e)

/-- Nonloop moments follow from the assumed finite offline optimum moment. -/
theorem integrable_nonloop_of_integrable_optimum {n : ℕ}
    (M : Matroid (Fin n)) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Weights n) (hV : Measurable V)
    (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e)
    (hopt : Integrable (fun ω => optimum M (V ω)) μ)
    (e : Fin n) (he : M.IsNonloop e) : Integrable (fun ω => V ω e) μ := by
  apply hopt.mono' ((measurable_pi_apply e).comp hV).aestronglyMeasurable
  filter_upwards [hVN] with ω hω
  change ‖V ω e‖ ≤ optimum M (V ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (hω e)]
  exact nonloop_weight_le_optimum M (V ω) e he

/-- Conversely, finite moments only on the nonloops suffice for finite E[OPT]. -/
theorem integrable_optimum_of_integrable_nonloops {n : ℕ}
    (M : Matroid (Fin n)) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → Weights n) (hV : Measurable V)
    (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e)
    (hmom : ∀ e, M.IsNonloop e → Integrable (fun ω => V ω e) μ) :
    Integrable (fun ω => optimum M (V ω)) μ := by
  classical
  have hsum : Integrable (fun ω =>
      ∑ e : Fin n, if M.IsNonloop e then V ω e else 0) μ := by
    apply integrable_finsetSum
    intro e _
    by_cases he : M.IsNonloop e
    · simpa only [ite_eq_left he] using hmom e he
    · simp only [ite_eq_right he]
      exact integrable_zero _ _ _
  apply hsum.mono' ((measurable_optimum M).comp hV).aestronglyMeasurable
  filter_upwards [hVN] with ω hω
  change ‖optimum M (V ω)‖ ≤ ∑ e : Fin n, if M.IsNonloop e then V ω e else 0
  rw [Real.norm_eq_abs, abs_of_nonneg (optimum_nonneg M (V ω))]
  exact optimum_le_sum_nonloops M (V ω) hω

/-- An exact criterion: loop moments are deliberately absent on the right. -/
theorem integrable_optimum_iff {n : ℕ} (M : Matroid (Fin n))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (V : Ω → Weights n) (hV : Measurable V)
    (hVN : ∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) :
    Integrable (fun ω => optimum M (V ω)) μ ↔
      ∀ e, M.IsNonloop e → Integrable (fun ω => V ω e) μ := by
  constructor
  · exact integrable_nonloop_of_integrable_optimum M μ V hV hVN
  · exact integrable_optimum_of_integrable_nonloops M μ V hV hVN

end MatroidProphet.DegenerateCases

end OAI
