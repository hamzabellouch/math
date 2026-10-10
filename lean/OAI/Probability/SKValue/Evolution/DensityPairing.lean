import Mathlib
import OAI.Probability.SKValue.Gaussian.DensityJump
import OAI.Probability.SKValue.Evolution.HeatDuality

namespace OAI

section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKValue
lemma exp_coleHopf {A:ℝ → ℝ} (hA:SmoothTerminal A) {c:ℝ} (hc:0<c) (t x:ℝ) :
    Real.exp (c*coleHopf c t A x)=heat t (fun y ↦ Real.exp (c*A y)) x := by
  simp only [coleHopf,ite_eq_right hc.ne']
  rw [mul_div_cancel₀ _ hc.ne']
  exact Real.exp_log (lipschitz_exp_integral_pos hA.lipschitz hc.le x (Real.sqrt t))

lemma ForwardDensityData.response_pairing (D:ForwardDensityData) {A f:ℝ → ℝ}
    (hA:SmoothTerminal A) (hf:BoundedSmooth f) {c t:ℝ} (hc:0<c) (ht:0≤t) :
    (∫ x,(Real.exp (c*coleHopf c t A x)*D.weight x)*responseJet c A f 0 t x)=
      ∫ x,(Real.exp (c*A x)*(D.evolve t ht).weight x)*f x := by
  have he (x:ℝ):(Real.exp (c*coleHopf c t A x)*D.weight x)*responseJet c A f 0 t x=
      D.weight x*heat t (fun y ↦ Real.exp (c*A y)*f y) x := by
    rw [exp_coleHopf hA hc]
    simp only [responseJet,iteratedDeriv_zero]
    have hn:heat t (fun y ↦ Real.exp (c*A y)) x≠0 :=
      (lipschitz_exp_integral_pos hA.lipschitz hc.le x (Real.sqrt t)).ne'
    field_simp [hn]
  simp_rw [he]
  have hh:=D.heat_duality (show ExpGrowth (fun x ↦ Real.exp (c*A x)*f x) from by
      simpa only [iteratedDeriv_zero] using weighted_growth hA hf hc.le 0)
    (hA.smooth.continuous.measurable.const_mul c |>.exp |>.mul hf.smooth.continuous.measurable) t
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [D.evolve_weight]
  ring

lemma ForwardDensityData.jump_density (D:ForwardDensityData) {A:ℝ → ℝ}
    (hA:SmoothTerminal A) (heven:∀ x,A (-x)=A x) {c d:ℝ} (hcd:c≤d) (x:ℝ) :
    Real.exp (d*A x)*(D.jump hA heven (d-c) (sub_nonneg.mpr hcd)).weight x=
      Real.exp (c*A x)*D.weight x := by
  rw [D.jump_weight]
  have he:d*A x+(-(d-c)*A x)=c*A x := by ring
  calc
    _ = (Real.exp (d*A x)*Real.exp (-(d-c)*A x))*D.weight x := by ring
    _ = _ := by rw [←Real.exp_add,he]

lemma gaussian_heat_zero {f:ℝ → ℝ} (hf:Measurable f) {t:ℝ} (ht:0<t) :
    heat t f 0=∫ x,gaussianPDFReal 0 t.toNNReal x*f x := by
  have hm:MeasurePreserving (fun z:ℝ ↦ 0+Real.sqrt t*z) standardGaussian (gaussianReal 0 t.toNNReal) :=
    (shiftedGaussian_hasLaw ht.le 0).measurePreserving (by fun_prop)
  have he:=(shiftedGaussian_hasLaw ht.le 0).integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_def] at he
  change (∫ z,f (0+Real.sqrt t*z) ∂standardGaussian)=_
  rw [he,gaussianReal_of_var_ne_zero _ (Real.toNNReal_pos.mpr ht).ne',
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (Eventually.of_forall (fun x ↦ by simp [gaussianPDF]))]
  simp only [toReal_gaussianPDF,smul_eq_mul]

lemma first_response_density {A f:ℝ → ℝ} (hA:SmoothTerminal A) (hf:BoundedSmooth f)
    {c t:ℝ} (hc:0<c) (ht:0<t) :
    responseJet c A f 0 t 0=
      Real.exp (-(c*coleHopf c t A 0))*(∫ x,(Real.exp (c*A x)*(ForwardDensityData.gaussian t ht).weight x)*f x) := by
  simp only [responseJet,iteratedDeriv_zero]
  have hm:Measurable (fun y ↦ Real.exp (c*A y)*f y) :=
    ((hA.smooth.continuous.measurable.const_mul c).exp.mul hf.smooth.continuous.measurable)
  rw [gaussian_heat_zero hm ht,←exp_coleHopf hA hc,Real.exp_neg]
  rw [div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ForwardDensityData.gaussian_weight]
  ring
end SKValue

end

end OAI
