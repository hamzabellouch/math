import OAI.Analysis.HyperbolicCones.Model

namespace OAI

noncomputable section

open Set Polynomial
open scoped ContDiff Matrix.Norms.L2Operator Topology

namespace Paper256

theorem timeScale_positive (η t : ℝ) (hη : 0 < η) : 0 < timeScale η t := by
  unfold timeScale
  positivity

theorem timeScale_endpoints (η : ℝ) : timeScale η 0 = 1 ∧ timeScale η 1 = 1 := by
  simp [timeScale]

theorem timeScale_strict_interior (η t : ℝ) (hη : 0 < η) (ht : t ∈ Ioo (0 : ℝ) 1) :
    1 < timeScale η t := by
  have hs : 0 < Real.sin (Real.pi * t) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
      (by nlinarith [Real.pi_pos, ht.2])
  unfold timeScale
  have := mul_pos hη (sq_pos_of_pos hs)
  linarith

theorem timeScale_smooth (η : ℝ) : ContDiff ℝ ∞ (timeScale η) := by
  unfold timeScale
  fun_prop

theorem deformedPolynomial_eval (a b η t x : ℝ) :
    (deformedPolynomial a b η t).eval x =
      (1 - timeScale η t * x / a) * (1 + timeScale η t * x / b) := by
  simp [deformedPolynomial, intervalPolynomial, div_eq_mul_inv]
  ring

theorem deformedPolynomial_eval_zero (a b η t : ℝ) :
    (deformedPolynomial a b η t).eval 0 = 1 := by
  simp [deformedPolynomial_eval]

theorem deformedPolynomial_factor (a b η t : ℝ) :
    deformedPolynomial a b η t =
      (1 - C (timeScale η t / a) * X) * (1 + C (timeScale η t / b) * X) := by
  simp [deformedPolynomial, intervalPolynomial, div_eq_mul_inv, map_mul]
  ring

theorem deformedPolynomial_scaled (a b η t : ℝ) :
    deformedPolynomial a b η t =
      intervalPolynomial (a / timeScale η t) (b / timeScale η t) := by
  rw [deformedPolynomial_factor]
  simp [intervalPolynomial, div_eq_mul_inv]

theorem deformedPolynomial_expanded (a b η t : ℝ) :
    deformedPolynomial a b η t =
      1 + C (timeScale η t * (b⁻¹ - a⁻¹)) * X +
        C (-(a⁻¹ * b⁻¹ * timeScale η t ^ 2)) * X ^ 2 := by
  rw [deformedPolynomial_factor]
  simp [div_eq_mul_inv, map_mul, map_sub, map_neg, map_pow]
  ring

theorem deformedCoefficients_eq (a b η t : ℝ) :
    deformedCoefficients a b η t =
      ![1, timeScale η t * (b⁻¹ - a⁻¹), -(a⁻¹ * b⁻¹ * timeScale η t ^ 2)] := by
  funext i
  fin_cases i <;> simp only [deformedCoefficients, deformedPolynomial_expanded,
    coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_one] <;> norm_num

theorem deformedCoefficients_smooth (a b η : ℝ) :
    ContDiff ℝ ∞ (deformedCoefficients a b η) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [deformedCoefficients_eq, timeScale] <;> fun_prop

theorem deformedPencil_eq (a b η t x : ℝ) :
    deformedPencil a b η t x =
      1 + (timeScale η t * x) • Matrix.diagonal ![-a⁻¹, b⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [deformedPencil, Matrix.diagonal, div_eq_mul_inv]
  ring

theorem deformedPencil_smooth (a b η : ℝ) :
    ContDiff ℝ ∞ (fun tx : ℝ × ℝ => deformedPencil a b η tx.1 tx.2) := by
  simp_rw [deformedPencil_eq]
  have hf : ContDiff ℝ ∞ (fun tx : ℝ × ℝ => timeScale η tx.1 * tx.2) := by
    unfold timeScale
    fun_prop
  exact contDiff_const.add (hf.smul contDiff_const)

theorem deformedPencil_det (a b η t x : ℝ) :
    Matrix.det (deformedPencil a b η t x) = (deformedPolynomial a b η t).eval x := by
  simp [deformedPencil, deformedPolynomial_eval]

theorem deformedPencil_zero (a b η t : ℝ) : deformedPencil a b η t 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [deformedPencil, Matrix.diagonal]

theorem deformedPolynomial_endpoints (a b η : ℝ) :
    deformedPolynomial a b η 0 = intervalPolynomial a b ∧
      deformedPolynomial a b η 1 = intervalPolynomial a b := by
  simp [deformedPolynomial, timeScale]

end Paper256

end

end OAI
