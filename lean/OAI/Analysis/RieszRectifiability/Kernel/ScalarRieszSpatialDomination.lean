import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedMeanZeroTail
import OAI.Analysis.RieszRectifiability.Kernel.ScalarRieszLocalBound

namespace OAI

/-!
# Spatial domination of scalar capped transforms

A uniform local bound and the mean-zero tail estimate combine into a measurable,
nonnegative majorant for compactly supported Schwartz tests. Global upper growth
makes this majorant integrable against the ambient measure, uniformly in the
positive truncation scales bounded by the support radius.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory SchwartzMap Metric Filter Topology Set

theorem exists_integrable_scalarCappedTransform_dominator (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient (p + 1))) (hμ : GlobalUpperGrowth (p + 1) C μ)
    (e a : Ambient (p + 1)) (H : ℝ) (hH : 0 < H)
    (g : 𝓢(Ambient (p + 1), ℝ)) (hmean : (∫ y, g y) = 0)
    (hgs : ∀ y, g y ≠ 0 → dist y a ≤ H) :
    ∃ D : Ambient (p + 1) → ℝ, Measurable D ∧ Integrable D μ ∧ (∀ x, 0 ≤ D x) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ H → ∀ x,
        ‖scalarCappedTransform (p + 1) volume e ε g x‖ ≤ D x := by
  obtain ⟨B, hB, hlocal⟩ := exists_uniform_local_scalarCappedTransform_bound p e g (‖a‖ + 2 * H)
  let A := (∫ y, |g y|) *
    ((2 ^ (p + 1 + 1) + (p + 1 + 1 : ℝ) * 2 ^ (p + 1 + 2)) * (‖e‖ * H))
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg (integral_nonneg fun _ => abs_nonneg _) (by positivity)
  let D : Ambient (p + 1) → ℝ := fun x =>
    (ball a (2 * H)).indicator (fun _ => B) x +
      A * (closedExterior a (2 * H)).indicator (inverseDistancePow (p + 2) a) x
  have hfinite : μ (ball a (2 * H)) ≠ ⊤ :=
    ne_of_lt ((hμ.2 a (2 * H) (by linarith)).trans_lt ENNReal.ofReal_lt_top)
  have hnear : IntegrableOn (fun _ : Ambient (p + 1) => B) (ball a (2 * H)) μ :=
    integrableOn_const hfinite
  have hfar := (inverseDistancePow_closedExterior_integrable_and_bound (p + 1) C μ hμ a (2 * H)
    (by linarith)).1
  have hDm : Measurable D :=
    (measurable_const.indicator measurableSet_ball).add
      (measurable_const.mul ((inverseDistancePow_measurable (p + 2) a).indicator
        (closedExterior_measurable a (2 * H))))
  have hDI : Integrable D μ :=
    (hnear.integrable_indicator measurableSet_ball).add
      ((hfar.integrable_indicator (closedExterior_measurable a (2 * H))).const_mul A)
  have hDn (x : Ambient (p + 1)) : 0 ≤ D x := by
    exact add_nonneg (indicator_nonneg (fun _ _ => hB) x)
      (mul_nonneg hA (indicator_nonneg (fun y _ => inverseDistancePow_nonneg _ _ y) x))
  refine ⟨D, hDm, hDI, hDn, ?_⟩
  intro ε hε hεH x
  by_cases hx : x ∈ ball a (2 * H)
  · have hxnorm : ‖x‖ ≤ ‖a‖ + 2 * H := by
      have ht' : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
        simpa only [sub_add_cancel] using! norm_add_le (x - a) a
      have hx' : ‖x - a‖ < 2 * H := by simpa only [mem_ball, dist_eq_norm] using! hx
      linarith
    dsimp only [D]
    rw [indicator_of_mem hx, Real.norm_eq_abs]
    apply (hlocal ε hε x hxnorm).trans
    exact le_add_of_nonneg_right (mul_nonneg hA
      (indicator_nonneg (fun y _ => inverseDistancePow_nonneg _ _ y) x))
  · have hxext : x ∈ closedExterior a (2 * H) := by
      simpa only [closedExterior, mem_ofPred_eq, mem_ball, not_lt, dist_comm x a] using! hx
    dsimp only [D]
    rw [indicator_of_notMem hx, zero_add, indicator_of_mem hxext, Real.norm_eq_abs]
    simpa only [A, Nat.cast_add, Nat.cast_one] using!
      scalarCappedTransform_mean_zero_tail (p + 1) volume e a H ε hH hε hεH g
        g.continuous.measurable g.integrable hmean hgs x hxext

end

end RieszRectifiability

end OAI
