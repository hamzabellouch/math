import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianSecondStep
import OAI.Probability.SKBarriers.Calculus.ParameterComposition
import OAI.Probability.SKBarriers.Calculus.ParameterIntegral
import OAI.Probability.SKBarriers.Calculus.ParameterLinear

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterSmooth
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def ParamRegular (f : P × E → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ ParamLinearGrowth f ∧ ParamExpGrowth (fderiv ℝ f) ∧
    ParamExpGrowth (fderiv ℝ (fderiv ℝ f))

theorem ParamRegular.const_mul {f : P × E → ℝ} (hf : ParamRegular f) (c : ℝ) :
    ParamRegular (fun z => c*f z) := by
  refine ⟨contDiff_const.mul hf.1,hf.2.1.const_mul c,?_,?_⟩
  · apply hf.2.2.1.of_norm_le (abs_nonneg c)
    intro z
    rw [((hf.1.differentiable (by norm_num) z).hasFDerivAt.const_mul c).fderiv]
    simp only [norm_smul,Real.norm_eq_abs]
    exact le_rfl
  · apply hf.2.2.2.of_norm_le (abs_nonneg c)
    intro z
    rw [fderiv_fderiv_const_mul f hf.1 c]
    simpa only [Real.norm_eq_abs] using ContinuousLinearMap.opNorm_smul_le c (fderiv ℝ (fderiv ℝ f) z)

theorem param_gaussian_smooth (f : P × (E × ℝ) → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth f) (hg₁ : ParamExpGrowth (fderiv ℝ f))
    (hg₂ : ParamExpGrowth (fderiv ℝ (fderiv ℝ f))) :
    let Z := fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1
    ContDiff ℝ 2 Z ∧ ParamExpGrowth (fderiv ℝ Z) ∧
      ParamExpGrowth (fderiv ℝ (fderiv ℝ Z)) := by
  let L : (P × E) × ℝ →L[ℝ] P × (E × ℝ) :=
    (ContinuousLinearEquiv.prodAssoc ℝ P E ℝ).toContinuousLinearMap
  let ι : P × (E × ℝ) → (P × E) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  let g := fun z => f (L z)
  have hc : ContDiff ℝ 2 g := hf.comp L.contDiff
  have hg' : ParamExpGrowth (fun z => g (ι z)) := hg
  have h₁ : ParamExpGrowth (fun z => fderiv ℝ g (ι z)) :=
    param_fderiv_compCLM_growth f L ι (hf.differentiable (by norm_num)) hg₁
  have h₂ : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ g) (ι z)) :=
    param_second_compCLM_growth f L ι hf hg₂
  exact ⟨param_contDiff_gaussian_integral g hc hg' h₁ h₂,
    param_fderiv_gaussian_integral_growth g (hc.of_le (by norm_num)) hg' h₁,
    param_second_gaussian_integral_growth g hc hg' h₁ h₂⟩

theorem ParamRegular.gaussian_integral {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f) :
    ParamRegular (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  have h := param_gaussian_smooth f hf.1 hf.2.1.expGrowth hf.2.2.1 hf.2.2.2
  exact ⟨h.1,hf.2.1.gaussian_integral,h.2⟩
end ParameterSmooth
end SK.Analytic

end
end

end

end OAI
