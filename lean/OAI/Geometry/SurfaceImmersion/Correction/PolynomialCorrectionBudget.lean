import OAI.Geometry.SurfaceImmersion.Correction.PolynomialFixedOrderThreshold
import OAI.Geometry.SurfaceImmersion.Correction.ExplicitCorrectionBudgetThreshold

namespace OAI

/-! Polynomial reciprocal control for preservation of the iteration budgets. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

lemma polynomial_inverse_min {f g : ℝ → ℝ}
    (hf : HasPolynomialBound (fun x => (f x)⁻¹))
    (hg : HasPolynomialBound (fun x => (g x)⁻¹))
    (hfp : ∀ x, 1 ≤ x → 0 < f x) (hgp : ∀ x, 1 ≤ x → 0 < g x) :
    HasPolynomialBound (fun x => (min (f x) (g x))⁻¹) := by
  apply HasPolynomialBound.of_le (hf.add hg)
  · intro x hx
    exact inv_nonneg.mpr (lt_min (hfp x hx) (hgp x hx)).le
  · intro x hx
    exact min_inverse_le_add (hfp x hx) (hgp x hx)

theorem correctionBudgetThreshold_inverse_polynomial
    (A B N L : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hB : HasPolynomialBound B) (hN : HasPolynomialBound N) (hL : HasPolynomialBound L)
    (hgap : ∀ x, 1 ≤ x → 1 ≤ B x-A x) :
    HasPolynomialBound (fun x => (correctionBudgetThreshold (A x) (B x) a (N x) (L x))⁻¹) := by
  let C₁ := fun x => N x*(1+B x)
  let C₂ := fun x => L x*(1+2*B x)
  have hC₁ : HasPolynomialBound C₁ := hN.mul ((polynomialBound_const zero_le_one).add hB)
  have hC₂ : HasPolynomialBound C₂ := hL.mul ((polynomialBound_const zero_le_one).add
    ((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul hB))
  have h₁ : HasPolynomialBound (fun x => (powerThreshold 5 |N x*(1+B x)| (B x-A x))⁻¹) := by
    apply powerThreshold_inverse_polynomial 5 _ _ C₁ (fun _ => 1) hC₁
      (polynomialBound_const zero_le_one) (fun _ _ => abs_nonneg _) (fun x hx => zero_lt_one.trans_le (hgap x hx))
    · intro x hx
      exact le_of_eq (abs_of_nonneg (hC₁.nonneg hx))
    · intro x hx
      simpa only [one_div,inv_one] using one_div_le_one_div_of_le zero_lt_one (hgap x hx)
  have h₂ : HasPolynomialBound (fun x => (powerThreshold 5 |L x*(1+2*B x)| (a/8))⁻¹) := by
    apply powerThreshold_inverse_polynomial 5 _ _ C₂ (fun _ => (a/8)⁻¹) hC₂
      (polynomialBound_const (by positivity)) (fun _ _ => abs_nonneg _)
      (fun _ _ => by positivity)
    · intro x hx
      exact le_of_eq (abs_of_nonneg (hC₂.nonneg hx))
    · intro _ _
      exact le_rfl
  apply polynomial_inverse_min h₁ h₂
  · intro x hx
    unfold powerThreshold
    exact pow_pos (lt_min zero_lt_one (div_pos (zero_lt_one.trans_le (hgap x hx)) (by positivity))) _
  · intro x _
    unfold powerThreshold
    exact pow_pos (lt_min zero_lt_one (div_pos (by positivity) (by positivity))) _

end ClosedSurfaceR4.ExactCorrection

end

end OAI
