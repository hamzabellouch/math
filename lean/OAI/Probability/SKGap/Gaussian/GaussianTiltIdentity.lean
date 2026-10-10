import Mathlib
import OAI.Probability.SKGap.Gaussian.GaussianRegression
import OAI.Probability.SKGap.Gaussian.ProductGaussianDensity

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

lemma gaussianPDFReal_standard_tilt (a x : ℝ) :
    gaussianPDFReal a 1 x=gaussianPDFReal 0 1 x*exp (a*x-a^2/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have he : -(x-a)^2/2= -x^2/2+(a*x-a^2/2) := by ring
  rw [he,exp_add]
  ring

lemma gaussianCoordinates_tilt {κ : Type*} [Fintype κ] (a : κ→ℝ) :
    (gaussianCoordinates κ).withDensity
      (fun g=>ENNReal.ofReal (exp ((∑ i,a i*g i)-(∑ i,a i^2)/2))) =
      Measure.pi (fun i=>gaussianReal (a i) 1) := by
  have hp (g : κ→ℝ) : (∏ i,gaussianPDFReal (a i) 1 (g i))=
      (∏ i,gaussianPDFReal 0 1 (g i))*exp ((∑ i,a i*g i)-(∑ i,a i^2)/2) := by
    calc
      _ = ∏ i, (gaussianPDFReal 0 1 (g i)*exp (a i*g i-a i^2/2)) :=
        Finset.prod_congr rfl (fun i _=>gaussianPDFReal_standard_tilt _ _)
      _ = _ := by
        rw [Finset.prod_mul_distrib,← exp_sum]
        congr 2
        rw [Finset.sum_sub_distrib,Finset.sum_div]
  change (Measure.pi (fun _ : κ=>gaussianReal 0 1)).withDensity _=_
  rw [GaussianDensity.pi_gaussian_density (fun _ : κ=>0) (fun _=>1) (fun _=>one_ne_zero),
    GaussianDensity.pi_gaussian_density a (fun _=>1) (fun _=>one_ne_zero)]
  rw [← withDensity_mul _ (GaussianDensity.measurable_productPDF _ _) (by fun_prop)]
  congr 1
  ext g
  simp only [Pi.mul_apply,hp]
  exact (ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _=>gaussianPDFReal_nonneg 0 1 (g i)))).symm

lemma gaussianCoordinates_shift_hasLaw {κ : Type*} [Fintype κ] (a : κ→ℝ) :
    HasLaw (fun g : κ→ℝ => fun i=>g i+a i)
      (Measure.pi (fun i=>gaussianReal (a i) 1)) (gaussianCoordinates κ) := by
  have hl (i : κ) : HasLaw (fun g : κ→ℝ=>g i+a i)
      (gaussianReal (a i) 1) (gaussianCoordinates κ) := by
    simpa only [zero_add] using gaussianReal_add_const (coordinate_hasLaw i) (a i)
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : κ=>aemeasurable_id)).comp
    (fun i=>fun x : ℝ=>x+a i) (fun _=>by fun_prop))

lemma gaussian_tilt_lintegral {κ : Type*} [Fintype κ] (a : κ→ℝ)
    (f : (κ→ℝ)→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g,ENNReal.ofReal (exp ((∑ i,a i*g i)-(∑ i,a i^2)/2))*f g ∂gaussianCoordinates κ)=
      ∫⁻ g,f (fun i=>g i+a i) ∂gaussianCoordinates κ := by
  have he := lintegral_withDensity_eq_lintegral_mul (gaussianCoordinates κ)
    (f:=fun g=>ENNReal.ofReal (exp ((∑ i,a i*g i)-(∑ i,a i^2)/2))) (by fun_prop) hf
  simp only [Pi.mul_apply] at he
  rw [← he,gaussianCoordinates_tilt]
  exact (gaussianCoordinates_shift_hasLaw a).lintegral_comp hf.aemeasurable |>.symm
end SKGap
end
end

end OAI
