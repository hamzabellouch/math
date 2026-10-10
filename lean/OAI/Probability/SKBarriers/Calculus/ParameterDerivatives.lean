import Mathlib
import OAI.Probability.SKBarriers.Gaussian.LogDerivatives
import OAI.Probability.SKBarriers.Calculus.ParameterGrowth

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterDerivatives
variable {P E X : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem ParamExpGrowth.smulRight {f : P × E → F →L[ℝ] ℝ} {g : P × E → G}
    (hf : ParamExpGrowth f) (hg : ParamExpGrowth g) :
    ParamExpGrowth (fun z => (f z).smulRight (g z)) := by
  apply (hf.norm.mul hg.norm).of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg _),abs_of_nonneg (norm_nonneg _)]
  exact le_of_eq (ContinuousLinearMap.norm_smulRight_apply _ _)

omit [NormedSpace ℝ F] in
theorem ParamExpGrowth.neg {f : P × E → F} (hf : ParamExpGrowth f) :
    ParamExpGrowth (fun z => -f z) := by
  apply hf.of_norm_le zero_le_one
  intro z
  simp

theorem param_fderiv_exp_growth (f : X → ℝ) (ι : P × E → X) (hf : Differentiable ℝ f)
    (hg : ParamExpGrowth (fun z => Real.exp (f (ι z))))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fun x => Real.exp (f x)) (ι z)) := by
  have H := hg.smul hg₁
  simpa only [funext (fun x => ((hf x).hasFDerivAt.exp).fderiv)] using H

theorem param_second_exp_growth (f : X → ℝ) (ι : P × E → X) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth (fun z => Real.exp (f (ι z))))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z)))
    (hg₂ : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ f) (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ (fun x => Real.exp (f x))) (ι z)) := by
  have H := (hg.smul hg₂).add ((hg.smul hg₁).smulRight hg₁)
  simpa only [fderiv_fderiv_exp f hf] using H

theorem param_fderiv_log_growth (f : X → ℝ) (ι : P × E → X) (hf : Differentiable ℝ f)
    (hp : ∀ x, f x ≠ 0) (hg : ParamExpGrowth (fun z => (f (ι z))⁻¹))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fun x => Real.log (f x)) (ι z)) := by
  have H := hg.smul hg₁
  have he : fderiv ℝ (fun x => Real.log (f x)) = fun x => (f x)⁻¹ • fderiv ℝ f x :=
    funext (fun x => ((hf x).hasFDerivAt.log (hp x)).fderiv)
  simpa only [he] using H

theorem param_second_log_growth (f : X → ℝ) (ι : P × E → X) (hf : ContDiff ℝ 2 f)
    (hp : ∀ x, f x ≠ 0) (hg : ParamExpGrowth (fun z => (f (ι z))⁻¹))
    (hg₁ : ParamExpGrowth (fun z => fderiv ℝ f (ι z)))
    (hg₂ : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ f) (ι z))) :
    ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ (fun x => Real.log (f x))) (ι z)) := by
  have H := (hg.smul hg₂).add (((hg.mul hg).neg.smul hg₁).smulRight hg₁)
  simpa only [fderiv_fderiv_log f hf hp,pow_two,mul_inv_rev,neg_mul] using H
end ParameterDerivatives
end SK.Analytic

end
end

end

end OAI
