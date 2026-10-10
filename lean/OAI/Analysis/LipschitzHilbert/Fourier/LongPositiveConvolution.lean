import OAI.Analysis.LipschitzHilbert.Fourier.PositiveConvolutionOscillation
import OAI.Analysis.LipschitzHilbert.Estimates.DyadicLongScales

namespace OAI

/-! Uniform long-scale oscillation of the actual positive error majorant. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem long_positiveConvolution_oscillation {N : ℕ}
    (f : Fin N → ℝ → ℝ) (hf : ∀ j, Measurable (f j)) {C L : ℝ}
    (hC : 0 ≤ C) (hL : 0 < L) (hbound : ∀ j s, ‖f j s‖ ≤ C)
    (u r : ℝ) (hr : 0 < r) {x y : ℝ}
    (hx : x ∈ Icc (u-r) (u+r)) (hy : y ∈ Icc (u-r) (u+r)) :
    |(∑ j : Fin N, if r < L / (2 : ℝ)^j.val then
      positiveConvolution (L / (2 : ℝ)^j.val) (f j) x else 0) -
      (∑ j : Fin N, if r < L / (2 : ℝ)^j.val then
      positiveConvolution (L / (2 : ℝ)^j.val) (f j) y else 0)| ≤
      240 * Real.pi * C := by
  let len := fun j : Fin N => L / (2 : ℝ)^j.val
  have hlen (j : Fin N) : 0 < len j := by dsimp [len]; positivity
  have hdist : |x-y| ≤ 2*r := abs_le.mpr ⟨by linarith [hx.1,hy.2], by linarith [hx.2,hy.1]⟩
  have heq : (∑ j : Fin N, if r < len j then
      ((60 * Real.pi * C) / len j) * |x-y| else 0) =
      ((60 * Real.pi * C) * |x-y|) * ∑ j : Fin N, if r < len j then (len j)⁻¹ else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : r < len j <;> simp only [hj, ite_true, ite_false, mul_zero]
    rw [div_eq_mul_inv]
    ring
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |(if r < len j then positiveConvolution (len j) (f j) x else 0) -
        (if r < len j then positiveConvolution (len j) (f j) y else 0)| := by
      simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ)
        (f := fun j : Fin N => (if r < len j then positiveConvolution (len j) (f j) x else 0) -
          (if r < len j then positiveConvolution (len j) (f j) y else 0))
    _ ≤ ∑ j : Fin N, if r < len j then ((60 * Real.pi * C) / len j) * |x-y| else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : r < len j
      · simp only [ite_eq_left hj]
        exact positiveConvolution_oscillation (hf j) hC (hlen j) (hbound j) x y (by linarith)
      · simp only [ite_eq_right hj, sub_zero, abs_zero, le_refl]
    _ = _ := heq
    _ ≤ ((60 * Real.pi * C) * (2*r)) * (2/r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdist (by positivity))
        (sum_long_dyadic_reciprocals N L r hL hr)
        (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)) (by positivity)
    _ = _ := by field_simp; ring

end LipschitzHilbert

end

end OAI
