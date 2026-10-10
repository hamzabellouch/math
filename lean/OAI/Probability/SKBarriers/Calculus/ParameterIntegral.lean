import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterGrowth
import OAI.Probability.SKBarriers.Calculus.ParameterWeakGrowth
import OAI.Probability.SKBarriers.Gaussian.LocalMarginal

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterIntegral
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem param_contDiff_gaussian_integral (f : (P × E) × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth (fun z : P × (E × ℝ) => f ((z.1,z.2.1),z.2.2)))
    (hg₁ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ f ((z.1,z.2.1),z.2.2)))
    (hg₂ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ (fderiv ℝ f) ((z.1,z.2.1),z.2.2))) :
    ContDiff ℝ 2 (fun z => ∫ y, f (z,y) ∂gaussianReal 0 1) := by
  exact contDiff_two_local_gaussian_integral_fderiv f hf hg.weakLocallyDominated
    hg₁.weakLocallyDominated hg₂.weakLocallyDominated

theorem param_fderiv_gaussian_integral_growth (f : (P × E) × ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hg : ParamExpGrowth (fun z : P × (E × ℝ) => f ((z.1,z.2.1),z.2.2)))
    (hg₁ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ f ((z.1,z.2.1),z.2.2))) :
    ParamExpGrowth (fderiv ℝ (fun z => ∫ y, f (z,y) ∂gaussianReal 0 1)) := by
  have H : ParamExpGrowth (fun z : P × E => ∫ y, ‖fderiv ℝ f (z,y)‖ ∂gaussianReal 0 1) :=
    (hg₁.weakNorm (fun _ => ContinuousLinearMap.opNorm_nonneg _)).gaussian_integral
  apply H.of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => ContinuousLinearMap.opNorm_nonneg (fderiv ℝ f (z,y))))]
  exact norm_fderiv_local_gaussian_integral_le f hf hg.weakLocallyDominated hg₁.weakLocallyDominated z

theorem param_second_gaussian_integral_growth (f : (P × E) × ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ParamExpGrowth (fun z : P × (E × ℝ) => f ((z.1,z.2.1),z.2.2)))
    (hg₁ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ f ((z.1,z.2.1),z.2.2)))
    (hg₂ : ParamExpGrowth (fun z : P × (E × ℝ) => fderiv ℝ (fderiv ℝ f) ((z.1,z.2.1),z.2.2))) :
    ParamExpGrowth (fderiv ℝ (fderiv ℝ (fun z => ∫ y, f (z,y) ∂gaussianReal 0 1))) := by
  have H : ParamExpGrowth (fun z : P × E => ∫ y, ‖fderiv ℝ (fderiv ℝ f) (z,y)‖ ∂gaussianReal 0 1) :=
    (hg₂.weakNorm (fun _ => ContinuousLinearMap.opNorm_nonneg _)).gaussian_integral
  apply H.of_norm_le zero_le_one
  intro z
  rw [one_mul,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun y => ContinuousLinearMap.opNorm_nonneg (fderiv ℝ (fderiv ℝ f) (z,y))))]
  exact norm_fderiv_fderiv_local_gaussian_integral_le f hf hg.weakLocallyDominated
    hg₁.weakLocallyDominated hg₂.weakLocallyDominated z
end ParameterIntegral
end SK.Analytic

end
end

end

end OAI
