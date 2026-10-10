import Mathlib
import OAI.Probability.SKGap.Terminal.SpinEnergy

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_quadratic_integrable_sharp {j : ℝ} (hj : j < 1) :
    Integrable (fun g : ℝ=>exp (j*g^2/2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),integrable_withDensity_iff
    (measurable_gaussianPDF 0 1) (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  have hi := (integrable_exp_neg_mul_sq (show 0 < (1-j)/2 by linarith)).const_mul (1/sqrt (2*Real.pi))
  have he : (fun g : ℝ=>exp (j*g^2/2)*gaussianPDFReal 0 1 g)=
      (fun g : ℝ=>(1/sqrt (2*Real.pi))*exp (-((1-j)/2)*g^2)) := by
    funext g
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_left_comm,← exp_add]
    congr 2 <;> ring
  rw [he]
  exact hi

lemma gaussian_spin_exponential_integrable (a : ℝ) {n : ℕ} (x : Spin n) :
    Integrable (fun g : ℝ=>exp (a*g*∑ i,spinValue (x i))) (gaussianReal 0 1) := by
  convert (integrable_exp_mul_gaussianReal (μ:=0) (v:=1) (a*∑ i,spinValue (x i))) using 1
  ext g;congr 1;ring

lemma spin_gaussian_linearization {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (x : Spin n) :
    exp (r/2*(∑ i,spinValue (x i))^2)=
      ∫ g : ℝ,exp (sqrt r*g*∑ i,spinValue (x i)) ∂gaussianReal 0 1 := by
  have he := mgf_gaussianReal (μ:=0) (v:=1) (X:=fun g : ℝ=>g) (p:=gaussianReal 0 1) (by simp)
    (sqrt r*∑ i,spinValue (x i))
  simp only [mgf,zero_mul,NNReal.coe_one,one_mul,zero_add,mul_pow,sq_sqrt hr] at he
  calc
    _ = exp (r*(∑ i,spinValue (x i))^2/2) := by congr 1;ring
    _ = ∫ g : ℝ,exp ((sqrt r*∑ i,spinValue (x i))*g) ∂gaussianReal 0 1 := he.symm
    _ = _ := by congr 1;ext g;congr 1;ring

lemma spin_quadratic_sum_bound {n : ℕ} {j r : ℝ} (hj : j < 1) (hr : 0 ≤ r)
    (hnr : (n:ℝ)*r ≤ j) :
    (∑ x : Spin n,exp (r/2*(∑ i,spinValue (x i))^2)) ≤
      (2:ℝ)^n*(∫ g : ℝ,exp (j*g^2/2) ∂gaussianReal 0 1) := by
  simp_rw [spin_gaussian_linearization hr]
  rw [← integral_finsetSum _ (fun x _=>gaussian_spin_exponential_integrable (sqrt r) x),
    ← integral_const_mul]
  apply integral_mono
    (integrable_finsetSum _ (fun x _=>gaussian_spin_exponential_integrable (sqrt r) x))
    ((gaussian_quadratic_integrable_sharp hj).const_mul _)
  intro g
  dsimp only []
  rw [spin_exponential_sum (sqrt r*g),mul_pow]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc
    (cosh (sqrt r*g))^n ≤ (exp ((sqrt r*g)^2/2))^n :=
      pow_le_pow_left₀ (cosh_pos _).le (cosh_le_exp_half_sq _) _
    _ = exp ((n:ℝ)*r*g^2/2) := by rw [← exp_nat_mul,mul_pow,sq_sqrt hr];congr 1;ring
    _ ≤ exp (j*g^2/2) := exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hnr (sq_nonneg g)])

end SKGap
end
end

end OAI
