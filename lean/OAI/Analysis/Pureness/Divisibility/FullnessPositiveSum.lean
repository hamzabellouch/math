import OAI.Analysis.Pureness.Divisibility.FullnessNormalization
import Mathlib.Analysis.CStarAlgebra.Module.Constructions

namespace OAI
namespace CuntzPureness
open scoped WithCStarModule InnerProductSpace
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]

theorem invertible_positive_sum_of_invertible_sum (h : A) (hh : 0 ≤ h) (r t : ι → A)
    (hS : IsUnit (∑ i, r i * h * t i)) :
    IsUnit (∑ i, star (t i) * h * t i) := by
  nontriviality A
  let S := ∑ i, r i * h * t i
  let q := ∑ i, star (t i) * h * t i
  let x : C⋆ᵐᵒᵈ(A, ι → A) := (WithCStarModule.equiv A _).symm (fun i => r i * CFC.sqrt h)
  let y : C⋆ᵐᵒᵈ(A, ι → A) := (WithCStarModule.equiv A _).symm (fun i => star (t i) * CFC.sqrt h)
  have hsqrt : star (CFC.sqrt h) = CFC.sqrt h := (CFC.sqrt_nonneg h).star_eq
  have hsquare (z : A) : CFC.sqrt h * (CFC.sqrt h * z) = h * z := by
    rw [← mul_assoc, CFC.sqrt_mul_sqrt_self h hh]
  have hxy : ⟪x, y⟫_A = star S := by
    simp [x, y, S, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, hh.star_eq, mul_assoc, hsquare]
  have hyx : ⟪y, x⟫_A = S := by
    simp [x, y, S, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, mul_assoc, hsquare]
  have hyy : ⟪y, y⟫_A = q := by
    simp [y, q, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, mul_assoc, hsquare]
  have hbound : star S * S ≤ ‖x‖ ^ 2 • q := by
    simpa only [hxy, hyx, hyy] using (CStarModule.inner_mul_inner_swap_le (A := A) (x := x) (y := y))
  have hpos : IsStrictlyPositive (star S * S) :=
    IsStrictlyPositive.iff_of_unital.mpr ⟨star_mul_self_nonneg S, hS.star.mul hS⟩
  have hunit : IsUnit (‖x‖ ^ 2 • q) := CStarAlgebra.isUnit_of_le _ hbound hpos
  have hx : x ≠ 0 := by
    intro hx
    have hzero : S = 0 := by simpa [hx] using hyx.symm
    have hS' : IsUnit S := hS
    exact not_isUnit_zero (hzero ▸ hS')
  have hc : ‖x‖ ^ 2 ≠ (0 : ℝ) := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcunit : IsUnit (algebraMap ℝ A (‖x‖ ^ 2)) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ A)
  rw [Algebra.smul_def] at hunit
  obtain ⟨u, hu⟩ := hcunit
  have huq := u⁻¹.isUnit.mul hunit
  simpa only [← hu, ← mul_assoc, Units.inv_mul, one_mul] using huq
end CuntzPureness

end OAI
