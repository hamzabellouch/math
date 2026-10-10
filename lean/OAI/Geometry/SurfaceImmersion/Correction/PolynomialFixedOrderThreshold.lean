import OAI.Geometry.SurfaceImmersion.Geometry.ExplicitFixedOrderThreshold
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanIteration

namespace OAI

/-! At each fixed order, the reciprocal of the scale threshold is
polynomial in the numerical data and reciprocal geometric margins. -/
noncomputable section
open scoped BigOperators
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

theorem fixedOrderNumericalBudget_polynomial (k : ℕ) (D B K : ℝ → ℝ) (C : ℕ → ℝ → ℝ)
    (hD : HasPolynomialBound D) (hB : HasPolynomialBound B) (hK : HasPolynomialBound K)
    (hC : ∀ m, HasPolynomialBound (C m)) :
    HasPolynomialBound (fun x => fixedOrderNumericalBudget k (D x) (B x) (K x) (fun m => C m x)) := by
  have hp := (((polynomialBound_const (show (0 : ℝ) ≤ 2 by norm_num)).add (hD.mul hB)).add hK).add
    (HasPolynomialBound.sum (Finset.range (k/2+1)) C (fun m _ => hC m))
  apply HasPolynomialBound.of_le hp
  · intro x hx
    have hd := hD.nonneg hx
    have hb := hB.nonneg hx
    have hk := hK.nonneg hx
    unfold fixedOrderNumericalBudget
    positivity
  · intro x hx
    have habs : ∀ m, |C m x| = C m x := fun m => abs_of_nonneg ((hC m).nonneg hx)
    simp only [fixedOrderNumericalBudget, habs]
    exact le_rfl

lemma min_inverse_le_add {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (min x y)⁻¹ ≤ x⁻¹+y⁻¹ := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    linarith [inv_nonneg.mpr hy.le]
  · rw [min_eq_right h]
    linarith [inv_nonneg.mpr hx.le]

theorem fixedOrderThreshold_inverse_polynomial (k : ℕ)
    (ρ a η D B K : ℝ → ℝ) (C : ℕ → ℝ → ℝ) (R A H : ℝ → ℝ)
    (hD : HasPolynomialBound D) (hB : HasPolynomialBound B) (hK : HasPolynomialBound K)
    (hC : ∀ m, HasPolynomialBound (C m))
    (hR : HasPolynomialBound R) (hA : HasPolynomialBound A) (hH : HasPolynomialBound H)
    (hρ : ∀ x, 1 ≤ x → 0 < ρ x) (ha : ∀ x, 1 ≤ x → 0 < a x)
    (hη : ∀ x, 1 ≤ x → 0 < η x)
    (hρR : ∀ x, 1 ≤ x → (ρ x)⁻¹ ≤ R x)
    (haA : ∀ x, 1 ≤ x → (a x)⁻¹ ≤ A x)
    (hηH : ∀ x, 1 ≤ x → (η x)⁻¹ ≤ H x) :
    HasPolynomialBound (fun x => (fixedOrderThreshold k (ρ x) (a x) (η x)
      (D x) (B x) (K x) (fun m => C m x))⁻¹) := by
  let S := fun x => fixedOrderNumericalBudget k (D x) (B x) (K x) (fun m => C m x)
  have hS : HasPolynomialBound S := fixedOrderNumericalBudget_polynomial k D B K C hD hB hK hC
  let b := fun x => min (η x) (min (ρ x/4) (a x/8))
  let P := fun x => H x+4*R x+8*A x
  have hP : HasPolynomialBound P := (hH.add
    ((polynomialBound_const (show (0 : ℝ) ≤ 4 by norm_num)).mul hR)).add
      ((polynomialBound_const (show (0 : ℝ) ≤ 8 by norm_num)).mul hA)
  apply powerThreshold_inverse_polynomial 10 S b S P hS hP
    (fun x hx => hS.nonneg hx) (fun x hx => lt_min (hη x hx)
      (lt_min (div_pos (hρ x hx) (by norm_num)) (div_pos (ha x hx) (by norm_num))))
    (fun _ _ => le_rfl)
  intro x hx
  have hρp : 0 < ρ x/4 := div_pos (hρ x hx) (by norm_num)
  have hap : 0 < a x/8 := div_pos (ha x hx) (by norm_num)
  have hρi : (ρ x/4)⁻¹ ≤ 4*R x := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (hρR x hx) (by norm_num)
  have hai : (a x/8)⁻¹ ≤ 8*A x := by
    rw [inv_div, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (haA x hx) (by norm_num)
  have hi := min_inverse_le_add (hη x hx) (lt_min hρp hap)
  have hj := min_inverse_le_add hρp hap
  change (min (η x) (min (ρ x/4) (a x/8)))⁻¹ ≤ H x+4*R x+8*A x
  linarith [hηH x hx]

end ClosedSurfaceR4.ExactCorrection

end

end OAI
