import Mathlib
import OAI.Probability.SKGap.Gaussian.ProductGaussianDensity
import OAI.Probability.SKGap.Posterior.GaussianChannel

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal
variable {n : ℕ}

lemma channel_pdf_tilt (a x : ℝ) :
    gaussianPDFReal a 1 x=gaussianPDFReal 0 1 x*exp (a*x-a^2/2) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  have he : -(x-a)^2/2= -x^2/2+(a*x-a^2/2) := by ring
  rw [he,exp_add]
  ring

lemma channelReference_tilt (a : Fin n→ℝ) :
    (channelReference n).withDensity
      (fun z=>ENNReal.ofReal (exp ((∑ i,a i*z i)-(∑ i,a i^2)/2))) =
      Measure.pi (fun i=>gaussianReal (a i) 1) := by
  have hp (z : Fin n→ℝ) : (∏ i,gaussianPDFReal (a i) 1 (z i))=
      (∏ i,gaussianPDFReal 0 1 (z i))*exp ((∑ i,a i*z i)-(∑ i,a i^2)/2) := by
    calc
      _ = ∏ i,(gaussianPDFReal 0 1 (z i)*exp (a i*z i-a i^2/2)) :=
        Finset.prod_congr rfl (fun i _=>channel_pdf_tilt _ _)
      _ = _ := by
        rw [Finset.prod_mul_distrib,← exp_sum]
        congr 2
        rw [Finset.sum_sub_distrib,Finset.sum_div]
  unfold channelReference
  rw [GaussianDensity.pi_gaussian_density (fun _ : Fin n=>0) (fun _=>1) (fun _=>one_ne_zero),
    GaussianDensity.pi_gaussian_density a (fun _=>1) (fun _=>one_ne_zero)]
  rw [← withDensity_mul _ (GaussianDensity.measurable_productPDF _ _) (by fun_prop)]
  congr 1
  ext z
  simp only [Pi.mul_apply,hp]
  exact (ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _=>gaussianPDFReal_nonneg 0 1 (z i)))).symm

lemma channel_shift_hasLaw (a : Fin n→ℝ) :
    HasLaw (fun z : Fin n→ℝ=>fun i=>z i+a i)
      (Measure.pi (fun i=>gaussianReal (a i) 1)) (channelReference n) := by
  have hl (i : Fin n) : HasLaw (fun z : Fin n→ℝ=>z i+a i)
      (gaussianReal (a i) 1) (channelReference n) := by
    have hc : HasLaw (fun z : Fin n→ℝ=>z i) (gaussianReal 0 1) (channelReference n) :=
      ⟨(measurable_pi_apply i).aemeasurable,(measurePreserving_eval (fun _ : Fin n=>gaussianReal 0 1) i).map_eq⟩
    simpa only [zero_add] using gaussianReal_add_const hc (a i)
  exact iIndepFun.hasLaw_pi hl ((iIndepFun_pi (fun _ : Fin n=>aemeasurable_id)).comp
    (fun i=>fun x : ℝ=>x+a i) (fun _=>by fun_prop))

lemma channel_likelihood_tilt {T : ℝ} (hT : 0 ≤ T) (x : Spin n) :
    (channelReference n).withDensity (fun z=>ENNReal.ofReal (gaussianChannelLikelihood T x z))=
      Measure.pi (fun i=>gaussianReal (sqrt T*spinValue (x i)) 1) := by
  have hs : (∑ i,(sqrt T*spinValue (x i))^2)=(n:ℝ)*T := by
    simp only [mul_pow,sq_sqrt hT,spinValue_sq,mul_one,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
  convert channelReference_tilt (fun i=>sqrt T*spinValue (x i)) using 1
  simp only [hs,gaussianChannelLikelihood]

lemma gaussianChannel_event (g : Disorder n) {T : ℝ} (hT : 0 ≤ T) (B : Set (Fin n→ℝ))
    (hB : MeasurableSet B) :
    gaussianChannelLaw g T B=∑ x,ENNReal.ofReal (mass g 0 x)*
      channelReference n ((fun z : Fin n→ℝ=>fun i=>z i+sqrt T*spinValue (x i)) ⁻¹' B) := by
  rw [gaussianChannelLaw,withDensity_apply _ hB]
  have hd (z : Fin n→ℝ) : ENNReal.ofReal (gaussianChannelDensity g T z)=
      ∑ x,ENNReal.ofReal (mass g 0 x)*ENNReal.ofReal (gaussianChannelLikelihood T x z) := by
    unfold gaussianChannelDensity
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _=>mul_nonneg (mass_nonneg g 0 x) (by unfold gaussianChannelLikelihood; positivity))]
    exact Finset.sum_congr rfl (fun x _=>ENNReal.ofReal_mul (mass_nonneg g 0 x))
  simp only [hd]
  rw [lintegral_finsetSum _ (fun x _=>by unfold gaussianChannelLikelihood; fun_prop)]
  apply Finset.sum_congr rfl
  intro x _
  rw [lintegral_const_mul _ (by unfold gaussianChannelLikelihood; fun_prop)]
  congr 1
  rw [← withDensity_apply _ hB,channel_likelihood_tilt hT]
  exact ((channel_shift_hasLaw (fun i=>sqrt T*spinValue (x i))).map_eq ▸
    Measure.map_apply (by fun_prop) hB)
end SKGap

end
end

end OAI
