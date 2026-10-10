import OAI.Probability.ClassicalON.AnnulusSmall

namespace OAI

noncomputable section
open scoped Real
namespace ClassicalON

theorem axisC_cube : axisC^3 = -axisC := by
  rw [axisC,← map_pow,← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisMatrixC,pow_succ,Matrix.mul_apply,Fin.sum_univ_succ]

theorem axisC_sq_mul : axisC^2*axisC = -axisC := by
  rw [← pow_succ,axisC_cube]

theorem axis_smul_mul (r : ℝ) (A B : SpinOperator 3) : (r • A)*B = r • (A*B) :=
  Algebra.smul_mul_assoc r A B

theorem axis_mul_smul (r : ℝ) (A B : SpinOperator 3) : A*(r • B) = r • (A*B) :=
  Algebra.mul_smul_comm r A B

def axisPolynomial (t : ℝ) : SpinOperator 3 :=
  1 + (Real.sin t) • axisC + (1-Real.cos t) • axisC^2

theorem axisPolynomial_derivative (t : ℝ) :
    HasDerivAt axisPolynomial (axisPolynomial t*axisC) t := by
  have h := ((hasDerivAt_const t (1:SpinOperator 3)).add ((Real.hasDerivAt_sin t).smul_const axisC)).add
    (((hasDerivAt_const t (1:ℝ)).sub (Real.hasDerivAt_cos t)).smul_const (axisC^2))
  apply h.congr_deriv
  change 0 + (Real.cos t) • axisC + (0 - -Real.sin t) • axisC^2 = axisPolynomial t*axisC
  simp only [axisPolynomial,add_mul,one_mul,axis_smul_mul,axisC_sq_mul,← pow_two]
  module

theorem axisPolynomial_commute (t : ℝ) : Commute (axisPolynomial t) axisC := by
  change axisPolynomial t*axisC = axisC*axisPolynomial t
  simp only [axisPolynomial,add_mul,mul_add,one_mul,mul_one,axis_smul_mul,
    axis_mul_smul,← pow_succ,← pow_succ']

theorem exp_axisC (t : ℝ) : NormedSpace.exp (t • axisC)=axisPolynomial t := by
  let f := fun t : ℝ => NormedSpace.exp (t • (-axisC))*axisPolynomial t
  have hd (t : ℝ) : HasDerivAt f 0 t := by
    apply ((hasDerivAt_exp_smul_const (-axisC) t).mul (axisPolynomial_derivative t)).congr_deriv
    rw [mul_assoc,neg_mul axisC (axisPolynomial t),← (axisPolynomial_commute t).eq]
    simp
  have he : f t = f 0 := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  have h0 : f 0 = 1 := by simp [f,axisPolynomial,zero_smul ℝ axisC,zero_smul ℝ (axisC^2)]
  rw [h0] at he
  have hm := congrArg (fun Q : SpinOperator 3 => NormedSpace.exp (t • axisC)*Q) he
  dsimp only [f] at hm
  rw [← mul_assoc,smul_neg,← NormedSpace.exp_add_of_commute (Commute.refl (t • axisC)).neg_right,
    add_neg_cancel,NormedSpace.exp_zero,mul_one,one_mul] at hm
  exact hm.symm

theorem exp_axisC_periodic : Function.Periodic (fun t : ℝ => NormedSpace.exp (t • axisC)) (2*Real.pi) := by
  intro t
  simp [exp_axisC,axisPolynomial,Real.sin_add_two_pi,Real.cos_add_two_pi]

theorem exp_axisC_pi_apply (v : EuclideanSpace ℝ (Fin 3)) :
    NormedSpace.exp (Real.pi • axisC) v = WithLp.toLp 2 ![-v 0,-v 1,v 2] := by
  rw [exp_axisC]
  ext i
  fin_cases i <;> simp [axisPolynomial,axisC_apply,pow_two] <;> ring

end ClassicalON

end

end OAI
