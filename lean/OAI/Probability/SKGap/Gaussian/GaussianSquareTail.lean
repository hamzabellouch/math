import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRegression

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_square_exp_integral :
    (∫ x : ℝ,exp (x^2/4) ∂gaussianReal 0 1) ≤ 2 := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul]
  have he : (fun x : ℝ=>gaussianPDFReal 0 1 x*exp (x^2/4))=
      (fun x : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*x^2)) := by
    funext x
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_assoc,← exp_add]
    congr 2 <;> ring
  rw [he,integral_const_mul,integral_gaussian]
  have hp := Real.pi_pos
  have h1 := sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have h2 := sq_sqrt (show 0 ≤ Real.pi/(1/4:ℝ) by positivity)
  have h3 := sqrt_nonneg (2*Real.pi)
  have h4 := sqrt_nonneg (Real.pi/(1/4:ℝ))
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (sqrt_pos.mpr (by positivity))).mpr
  nlinarith

lemma gaussian_square_exp_integrable :
    Integrable (fun x : ℝ=>exp (x^2/4)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero),integrable_withDensity_iff
    (measurable_gaussianPDF 0 1) (ae_of_all _ (fun y=>by simp [gaussianPDF]))]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  have hi := (integrable_exp_neg_mul_sq (show (0:ℝ) < 1/4 by norm_num)).const_mul (1/sqrt (2*Real.pi))
  have he : (fun g : ℝ=>exp (g^2/4)*gaussianPDFReal 0 1 g)=
      (fun g : ℝ=>(1/sqrt (2*Real.pi))*exp (-(1/4:ℝ)*g^2)) := by
    funext g
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    rw [mul_left_comm,← exp_add]
    congr 2 <;> ring
  rw [he]
  exact hi

lemma product_gaussian_square_exp_integral {ι : Type*} [Fintype ι] :
    (∫ g : ι→ℝ,exp ((∑ i,g i^2)/4) ∂Measure.pi (fun _ : ι=>gaussianReal 0 1)) ≤
      exp ((Fintype.card ι:ℝ)*log 2) := by
  have he (g : ι→ℝ) : exp ((∑ i,g i^2)/4)=∏ i,exp (g i^2/4) := by
    rw [← exp_sum,Finset.sum_div]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (f:=fun _ : ι=>fun x : ℝ=>exp (x^2/4))]
  calc
    _ ≤ ∏ _i : ι,(2:ℝ) := Finset.prod_le_prod₀
      (fun i _=>integral_nonneg (fun x=>(exp_pos _).le))
      (fun i _=>gaussian_square_exp_integral)
    _ = _ := by rw [Finset.prod_const,Finset.card_univ,exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]

lemma product_gaussian_square_exp_integrable {ι : Type*} [Fintype ι] :
    Integrable (fun g : ι→ℝ=>exp ((∑ i,g i^2)/4))
      (Measure.pi (fun _ : ι=>gaussianReal 0 1)) := by
  have hi := Integrable.fintype_prod (fun _ : ι=>gaussian_square_exp_integrable)
  convert hi using 1
  ext g
  rw [← exp_sum,Finset.sum_div]

lemma product_gaussian_square_tail {ι : Type*} [Fintype ι] (t : ℝ) :
    (Measure.pi (fun _ : ι=>gaussianReal 0 1)).real {g | t < ∑ i,g i^2} ≤
      exp (-t/4+(Fintype.card ι:ℝ)*log 2) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (Measure.pi (fun _ : ι=>gaussianReal 0 1))
      (fun g=>(exp_pos ((∑ i,g i^2)/4)).le)) product_gaussian_square_exp_integrable (exp (t/4))
  have hs : {g : ι→ℝ| t < ∑ i,g i^2} ⊆ {g | exp (t/4) ≤ exp ((∑ i,g i^2)/4)} := by
    intro g hg
    exact exp_le_exp.mpr (by linarith only [show t < ∑ i,g i^2 from hg])
  have hb := (mul_le_mul_of_nonneg_left (measureReal_mono hs)
    (exp_pos (t/4)).le).trans (hm.trans product_gaussian_square_exp_integral)
  rw [show -t/4+(Fintype.card ι:ℝ)*log 2=(Fintype.card ι:ℝ)*log 2-t/4 by ring,exp_sub]
  apply (le_div_iff₀ (exp_pos _)).mpr
  simpa only [mul_comm] using hb
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal
variable {κ : Type*} [Fintype κ]

lemma gaussian_scaled_coordinates_hasLaw {r : ℝ} (hr : 0 ≤ r) :
    HasLaw (fun g : κ→ℝ=>fun k=>sqrt r*g k)
      (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r))) (gaussianCoordinates κ) := by
  have hl (k : κ) : HasLaw (fun g : κ→ℝ=>sqrt r*g k)
      (gaussianReal 0 (Real.toNNReal r)) (gaussianCoordinates κ) := by
    have h := gaussianReal_const_mul (coordinate_hasLaw (κ:=κ) k) (sqrt r)
    have hv : (⟨(sqrt r)^2,sq_nonneg _⟩:ℝ≥0)*1=Real.toNNReal r := by
      apply NNReal.eq
      change (sqrt r)^2*1=↑(Real.toNNReal r)
      rw [mul_one,sq_sqrt hr,Real.coe_toNNReal _ hr]
    rw [mul_zero] at h
    convert h using 1
    exact congrArg (gaussianReal 0) hv.symm
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : κ=>aemeasurable_id)).comp
    (fun _=>fun x : ℝ=>sqrt r*x) (fun _=>by fun_prop))

lemma scaled_gaussian_square_tail {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (Measure.pi (fun _ : κ=>gaussianReal 0 (Real.toNNReal r))).real {g | t < ∑ i,g i^2} ≤
      exp (-t/(4*r)+(Fintype.card κ:ℝ)*log 2) := by
  have hm : MeasurableSet {g : κ→ℝ | t < ∑ i,g i^2} := by measurability
  rw [← (gaussian_scaled_coordinates_hasLaw (κ:=κ) hr.le).measureReal_eq hm]
  have he : {g : κ→ℝ | t < ∑ i,(sqrt r*g i)^2}={g | t/r < ∑ i,g i^2} := by
    ext g
    simp only [Set.mem_ofPred_eq,mul_pow,sq_sqrt hr.le,← Finset.mul_sum]
    rw [div_lt_iff₀ hr,mul_comm]
  rw [he]
  simpa only [gaussianCoordinates,neg_div,div_div,mul_comm r (4:ℝ)] using
    product_gaussian_square_tail (ι:=κ) (t/r)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

lemma gaussian_real_square_tail {r : ℝ} (hr : 0 < r) (t : ℝ) :
    (gaussianReal 0 (Real.toNNReal r)).real {x : ℝ | t < x^2} ≤ exp (-t/(4*r)+log 2) := by
  have h : HasLaw (fun v : Unit→ℝ=>v ()) (gaussianReal 0 (Real.toNNReal r))
      (Measure.pi (fun _ : Unit=>gaussianReal 0 (Real.toNNReal r))) :=
    ⟨(measurable_pi_apply ()).aemeasurable,(measurePreserving_eval (fun _ : Unit=>gaussianReal 0 (Real.toNNReal r)) ()).map_eq⟩
  rw [← h.measureReal_eq (by measurability : MeasurableSet {x : ℝ | t < x^2})]
  simpa using scaled_gaussian_square_tail (κ:=Unit) hr t

lemma gaussian_real_abs_tail {r : ℝ} (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
    (gaussianReal 0 (Real.toNNReal r)).real {x : ℝ | d < |x|} ≤ 2*exp (-d^2/(4*r)) := by
  have he : {x : ℝ | d < |x|}={x | d^2 < x^2} := by
    ext x
    simpa only [Set.mem_ofPred_eq,sq_abs] using (sq_lt_sq₀ hd (abs_nonneg x)).symm
  rw [he]
  apply (gaussian_real_square_tail hr (d^2)).trans_eq
  rw [exp_add,exp_log (by norm_num : (0:ℝ) < 2),mul_comm]
end SKGap
end
end

end OAI
