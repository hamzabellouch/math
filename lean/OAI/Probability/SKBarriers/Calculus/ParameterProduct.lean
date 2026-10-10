import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
theorem ParamExpGrowth.weakSmul {P E F : Type} [NormedAddCommGroup P]
    [NormedAddCommGroup E] [Norm F] [SMul ℝ F] {f : P × E → ℝ} {g : P × E → F}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g)
    (hn : ∀ z, 0 ≤ ‖g z‖) (hm : ∀ z, ‖f z • g z‖ ≤ ‖f z‖*‖g z‖) :
    ParamExpGrowth (fun z => f z • g z) := by
  apply (hf.norm.mul (hg.weakNorm hn)).of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg (f z)),abs_of_nonneg (hn z)]
  exact hm z

section ParameterProduct
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParamSmooth.mul {f g : P × E → ℝ} (hf : ParamSmooth f) (hg : ParamSmooth g) :
    ParamSmooth (fun z => f z*g z) := by
  have hd := hf.1.differentiable (by norm_num)
  have he := hg.1.differentiable (by norm_num)
  have hdd := (hf.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hee := (hg.1.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h₁ : fderiv ℝ (fun z => f z*g z) = fun z =>
      f z • fderiv ℝ g z+g z • fderiv ℝ f z := by
    funext z
    exact ((hd z).hasFDerivAt.fun_mul (he z).hasFDerivAt).fderiv
  have h₂ : fderiv ℝ (fderiv ℝ (fun z => f z*g z)) = fun z =>
      (f z • fderiv ℝ (fderiv ℝ g) z+(fderiv ℝ f z).smulRight (fderiv ℝ g z))+
      (g z • fderiv ℝ (fderiv ℝ f) z+(fderiv ℝ g z).smulRight (fderiv ℝ f z)) := by
    rw [h₁]
    funext z
    exact (((hd z).hasFDerivAt.fun_smul (hee z).hasFDerivAt).fun_add
      ((he z).hasFDerivAt.fun_smul (hdd z).hasFDerivAt)).fderiv
  refine ⟨hf.1.mul hg.1,hf.2.1.mul hg.2.1,?_,?_⟩
  · rw [h₁]
    exact (hf.2.1.smul hg.2.2.1).add (hg.2.1.smul hf.2.2.1)
  · rw [h₂]
    exact ((hf.2.1.weakSmul hg.2.2.2 (fun _ => ContinuousLinearMap.opNorm_nonneg _)
      (fun _ => ContinuousLinearMap.opNorm_smul_le _ _)).weakAdd (hf.2.2.1.smulRight hg.2.2.1)
      (fun _ => ContinuousLinearMap.opNorm_add_le _ _)).weakAdd
      ((hg.2.1.weakSmul hf.2.2.2 (fun _ => ContinuousLinearMap.opNorm_nonneg _)
        (fun _ => ContinuousLinearMap.opNorm_smul_le _ _)).weakAdd (hg.2.2.1.smulRight hf.2.2.1)
        (fun _ => ContinuousLinearMap.opNorm_add_le _ _))
      (fun _ => ContinuousLinearMap.opNorm_add_le _ _)

theorem ParamSmooth.const_mul {f : P × E → ℝ} (hf : ParamSmooth f) (c : ℝ) :
    ParamSmooth (fun z => c*f z) := (paramSmooth_const c).mul hf

theorem ParamSmooth.gaussian_integral {f : P × (E × ℝ) → ℝ} (hf : ParamSmooth f) :
    ParamSmooth (fun z : P × E => ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1) := by
  have h := param_gaussian_smooth f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
  exact ⟨h.1,hf.2.1.gaussian_integral,h.2⟩
end ParameterProduct
end SK.Analytic

end
end

end

end OAI
