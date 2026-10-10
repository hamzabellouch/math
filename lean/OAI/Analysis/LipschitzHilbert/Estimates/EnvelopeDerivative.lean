import OAI.Analysis.LipschitzHilbert.Estimates.PolynomialEnvelope
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! Horizontal derivatives of the fixed rational packet envelope. -/

noncomputable section

namespace LipschitzHilbert

theorem lineEnvelope_three_hasDerivAt (a l x : ℝ) :
    HasDerivAt (lineEnvelope a l 3)
      ((-6 / l) * ((x-a)/l) * ((1+((x-a)/l)^2)^4)⁻¹) x := by
  have ht := ((hasDerivAt_id x).sub_const a).div_const l
  have hb := (ht.pow 2).const_add 1
  have hbase : 1 + ((x-a)/l)^2 ≠ 0 := by positivity
  have hd := (hb.pow 3).inv (pow_ne_zero 3 hbase)
  convert hd using 1
  · rfl
  · simp only [Pi.pow_apply, id_eq, Nat.reduceSub, Nat.cast_ofNat, pow_one]
    set t := (x-a)/l
    field_simp
    ring

theorem lineEnvelope_three_derivative_bound (a l x : ℝ) (hl : 0 < l) :
    |deriv (lineEnvelope a l 3) x| ≤ (6 / l) * lineEnvelope a l 3 x := by
  rw [(lineEnvelope_three_hasDerivAt a l x).deriv]
  let t := (x-a)/l
  have hb : 0 < 1+t^2 := by positivity
  have ht : |t| ≤ 1+t^2 := by nlinarith [sq_nonneg (|t|-1), sq_abs t]
  have heq : |(-6/l) * t * ((1+t^2)^4)⁻¹| =
      (6/l) * |t| * ((1+t^2)^4)⁻¹ := by
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 6),
      abs_of_pos hl, abs_of_nonneg (by positivity : 0 ≤ ((1+t^2)^4)⁻¹)]
  change |(-6/l) * t * ((1+t^2)^4)⁻¹| ≤ (6/l) * ((1+t^2)^3)⁻¹
  rw [heq]
  calc
    _ ≤ (6/l) * (1+t^2) * ((1+t^2)^4)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by positivity)) (by positivity)
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
