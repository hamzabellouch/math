import OAI.Analysis.LipschitzHilbert.Estimates.DyadicLongScales
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! Spatial oscillation after summing the actual dyadic long scales. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

theorem long_dyadic_sum_oscillation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (f : Fin N → ℝ → E) (L u r C : ℝ)
    (hL : 0 < L) (hr : 0 < r) (hC : 0 ≤ C)
    (hf : ∀ j x, DifferentiableAt ℝ (f j) x)
    (hderiv : ∀ j x, ‖deriv (f j) x‖ ≤ C / (L / (2 : ℝ) ^ j.val))
    {x y : ℝ} (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    ‖(∑ j : Fin N, if r < L / (2 : ℝ) ^ j.val then f j x else 0) -
      ∑ j : Fin N, if r < L / (2 : ℝ) ^ j.val then f j y else 0‖ ≤ 4*C := by
  let len := fun j : Fin N => L / (2 : ℝ) ^ j.val
  have hbound (j : Fin N) : ‖f j x - f j y‖ ≤ (C / len j) * |x-y| := by
    simpa only [Real.norm_eq_abs] using (convex_Icc (u-r) (u+r)).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hf j x) (fun x _ => hderiv j x) hy hx
  have hdist : |x-y| ≤ 2*r := abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩
  have heq : (∑ j : Fin N, if r < len j then (C / len j) * |x-y| else 0) =
      (C * |x-y|) * ∑ j : Fin N, if r < len j then (len j)⁻¹ else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : r < len j <;> simp only [hj, ite_true, ite_false, mul_zero]
    rw [div_eq_mul_inv]
    ring
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, ‖(if r < len j then f j x else 0) -
        (if r < len j then f j y else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin N, if r < len j then (C / len j) * |x-y| else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : r < len j
      · simpa only [ite_eq_left hj] using hbound j
      · simp only [ite_eq_right hj, sub_zero, norm_zero, le_refl]
    _ = _ := heq
    _ ≤ (C * (2*r)) * (2/r) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hdist hC)
        (sum_long_dyadic_reciprocals N L r hL hr)
        (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)) (by positivity)
    _ = 4*C := by field_simp; ring

end LipschitzHilbert

end

end OAI
