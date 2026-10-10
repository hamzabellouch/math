import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianStepCalculus
import OAI.Probability.SKBarriers.Gaussian.LocalMarginal

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section LocalStepDerivative
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_local_gaussianStep {f : E × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : GaussianLocallyDominated f) (hg₁ : GaussianLocallyDominated (fderiv ℝ f))
    (m : ℝ) (he : GaussianLocallyDominated (fun z => Real.exp (m*f z)))
    (he₁ : GaussianLocallyDominated (fderiv ℝ (fun z => Real.exp (m*f z)))) (x : E) :
    fderiv ℝ (gaussianStep m f) x =
      ∫ y, leftRestrict (fderiv ℝ f (x,y)) ∂gaussianStepLaw m f x := by
  have hd := hf.differentiable (by norm_num)
  by_cases hm : m = 0
  · subst m
    rw [gaussianStepLaw_zero]
    have hfun : SK.Analytic.gaussianStep 0 f = (fun x => ∫ y, f (x,y) ∂gaussianReal 0 1) := by
      funext x
      simp only [SK.Analytic.gaussianStep,ite_true]
    rw [hfun]
    exact fderiv_local_gaussian_integral f hf hg hg₁ x
  · let Z : E → ℝ := fun x => ∫ y, Real.exp (m*f (x,y)) ∂gaussianReal 0 1
    have hc : ContDiff ℝ 1 (fun z => Real.exp (m*f z)) := (contDiff_const.mul hf).exp
    have hp : Z x ≠ 0 := (integral_exp_pos (he.integrable_section hc.continuous x)).ne'
    have hi := hasFDerivAt_local_gaussian_integral (fun z => Real.exp (m*f z)) _
      hc.continuous (leftRestrict.continuous.comp
        ((hc.fderiv_right (m := 0) (by norm_num)).continuous)) he (he₁.clm leftRestrict)
      (leftRestrict_hasFDerivAt _ (hc.differentiable (by norm_num))) x
    have hfun : gaussianStep m f = fun x => Real.log (Z x)/m := by
      funext x
      simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,Z]
    rw [hfun]
    have hder := (hi.log hp).mul_const m⁻¹
    simp only [div_eq_mul_inv] at ⊢
    rw [hder.fderiv]
    rw [← integral_smul,← integral_smul,gaussianStepLaw,integral_tilted]
    apply integral_congr_ae
    filter_upwards [] with y
    have hdexp := ((hd (x,y)).hasFDerivAt.const_mul m).exp.fderiv
    simp only [Function.comp_apply]
    rw [hdexp]
    ext v
    simp only [smul_apply,smul_eq_mul,leftRestrict,
      ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply]
    dsimp only [Z] at hp ⊢
    field_simp [hm,hp]
end LocalStepDerivative
end SK.Analytic

end
end

end

end OAI
