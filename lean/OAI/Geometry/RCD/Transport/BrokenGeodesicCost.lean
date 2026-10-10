import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! # The two-leg energy and its equality case -/

namespace RegularPointCoordinates

theorem two_leg_cost_identity (A B C t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    t*(1-t)*(A^2/t+B^2/(1-t)-C^2) =
      ((1-t)*A-t*B)^2+t*(1-t)*((A+B)^2-C^2) := by
  field_simp [ht.ne', (sub_pos.mpr ht1).ne']
  ring

theorem two_leg_cost_nonneg {A B C t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (htriangle : C ≤ A+B) (ht : 0 < t) (ht1 : t < 1) :
    0 ≤ A^2/t+B^2/(1-t)-C^2 := by
  have htime : 0 < t*(1-t) := mul_pos ht (sub_pos.mpr ht1)
  have hgap : 0 ≤ (A+B)^2-C^2 := sub_nonneg.mpr ((sq_le_sq₀ hC (add_nonneg hA hB)).mpr htriangle)
  apply nonneg_of_mul_nonneg_left _ htime
  rw [mul_comm]
  rw [two_leg_cost_identity A B C t ht ht1]
  exact add_nonneg (sq_nonneg _) (mul_nonneg htime.le hgap)

theorem two_leg_cost_zero {A B C t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (htriangle : C ≤ A+B) (ht : 0 < t) (ht1 : t < 1)
    (he : A^2/t+B^2/(1-t)-C^2=0) : A=t*C ∧ B=(1-t)*C := by
  have htime : 0 < t*(1-t) := mul_pos ht (sub_pos.mpr ht1)
  have hgap : 0 ≤ (A+B)^2-C^2 := sub_nonneg.mpr ((sq_le_sq₀ hC (add_nonneg hA hB)).mpr htriangle)
  have hid := two_leg_cost_identity A B C t ht ht1
  rw [he,mul_zero] at hid
  have hz := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (mul_nonneg htime.le hgap)).mp hid.symm
  have hlin : (1-t)*A-t*B=0 := sq_eq_zero_iff.mp hz.1
  have hsq : (A+B)^2-C^2=0 := (mul_eq_zero.mp hz.2).resolve_left htime.ne'
  have hsum : A+B=C := by nlinarith
  rw [← hsum]
  constructor <;> nlinarith only [hlin]

end RegularPointCoordinates

end OAI
