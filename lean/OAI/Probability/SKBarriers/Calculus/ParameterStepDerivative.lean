import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianAverage
import OAI.Probability.SKBarriers.Calculus.ParameterAlgebra
import OAI.Probability.SKBarriers.Calculus.ParameterSmooth
import OAI.Probability.SKBarriers.Scalar.LocalStepDerivative

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterStepDerivative
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem param_reassoc_fderiv_growth {f : P × (E × ℝ) → ℝ}
    (hf : Differentiable ℝ f) (hg : ParamExpGrowth (fderiv ℝ f)) :
    ParamExpGrowth (fun z : P × (E × ℝ) =>
      fderiv ℝ (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) ((z.1,z.2.1),z.2.2)) := by
  let L : (P × E) × ℝ →L[ℝ] P × (E × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).toContinuousLinearMap
  let ι : P × (E × ℝ) → (P × E) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  have h : ParamExpGrowth (fun z => fderiv ℝ (fun w => f (L w)) (ι z)) :=
    param_fderiv_compCLM_growth f L ι hf hg
  exact h

theorem ParamExpGrowth.integrable_paramStepLaw {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f)
    {g : P × (E × ℝ) → F} (hg : ParamExpGrowth g) (hc : Continuous g)
    (m : ℝ) (z : P × E) : Integrable (fun y => g (z.1,(z.2,y)))
      (gaussianStepLaw m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) z) := by
  have he := hf.2.1.exp_mul m
  have hce : Continuous (fun w : (P × E) × ℝ => Real.exp (m*f (w.1.1,(w.1.2,w.2)))) :=
    Real.continuous_exp.comp (continuous_const.mul (hf.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))
  rw [gaussianStepLaw,integrable_tilted_iff (he.weakLocallyDominated.integrable_section hce z)]
  exact (he.smul hg).weakLocallyDominated.integrable_section (hce.smul
    (hc.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))) z

theorem ParamRegular.fderiv_gaussianStep {f : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (m : ℝ) (z : P × E) :
    fderiv ℝ (SK.Analytic.gaussianStep m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2)))) z =
      ∫ y, leftRestrict (fderiv ℝ (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) (z,y))
        ∂gaussianStepLaw m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2))) z := by
  have hg₁ := param_reassoc_fderiv_growth (hf.1.differentiable (by norm_num)) hf.2.2.1
  have he := (hf.const_mul m).expSmooth
  have he₁ := param_reassoc_fderiv_growth (he.1.differentiable (by norm_num)) he.2.2.1
  apply fderiv_local_gaussianStep
  · exact (hf.1.comp (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).contDiff).of_le (by norm_num)
  · exact hf.2.1.expGrowth.weakLocallyDominated
  · exact hg₁.weakLocallyDominated
  · exact he.2.1.weakLocallyDominated
  · exact he₁.weakLocallyDominated

theorem ParamRegular.parameterDerivative_gaussianStep {f : P × (E × ℝ) → ℝ}
    (hf : ParamRegular f) (m : ℝ) (z : P × E) (v : P) :
    fderiv ℝ (SK.Analytic.gaussianStep m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2)))) z (v,0) =
      gaussianAverage m (fun w : (P × E) × ℝ => f (w.1.1,(w.1.2,w.2)))
        (fun w : (P × E) × ℝ => fderiv ℝ f (w.1.1,(w.1.2,w.2)) (v,0)) z := by
  let L : (P × E) × ℝ →L[ℝ] P × (E × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).toContinuousLinearMap
  let g := fun w : (P × E) × ℝ => f (L w)
  have hcg : ContDiff ℝ 2 g := hf.1.comp L.contDiff
  have hg := param_reassoc_fderiv_growth (hf.1.differentiable (by norm_num)) hf.2.2.1
  have hi := (hg.clm leftRestrict).integrable_paramStepLaw hf
    ((leftRestrict.continuous.comp (hcg.fderiv_right (m := 1) (by norm_num)).continuous).comp
      (continuous_fst.prodMk continuous_snd.fst |>.prodMk continuous_snd.snd)) m z
  rw [hf.fderiv_gaussianStep,ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [] with y
  have hD := ((hf.1.differentiable (by norm_num) (L (z,y))).hasFDerivAt.comp (z,y) L.hasFDerivAt).fderiv
  change leftRestrict (fderiv ℝ g (z,y)) (v,0) = _
  change fderiv ℝ g (z,y) = _ at hD
  rw [hD]
  rfl
end ParameterStepDerivative
end SK.Analytic

end
end

end

end OAI
