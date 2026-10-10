import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterDerivatives
import OAI.Probability.SKBarriers.Calculus.ParameterInverse
import OAI.Probability.SKBarriers.Calculus.ParameterSmooth

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterRecursion
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ParamRegular.log_gaussian_exp {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f) :
    ParamRegular (fun z : P × E => Real.log
      (∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1)) := by
  have hg : ParamExpGrowth (fun z => Real.exp (f z)) := by
    simpa only [one_mul] using hf.2.1.exp_mul 1
  have h₁ := param_fderiv_exp_growth f id (hf.1.differentiable (by norm_num)) hg hf.2.2.1
  have h₂ := param_second_exp_growth f id hf.1 hg hf.2.2.1 hf.2.2.2
  let Z := fun z : P × E => ∫ y, Real.exp (f (z.1,(z.2,y))) ∂gaussianReal 0 1
  have hZ := param_gaussian_smooth (fun z => Real.exp (f z)) hf.1.exp hg h₁ h₂
  have hp (z : P × E) : Z z ≠ 0 := by
    apply (integral_exp_pos _).ne'
    apply hg.weakLocallyDominated.integrable_section
    exact Real.continuous_exp.comp (hf.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)))
  have hi : ParamExpGrowth (fun z => (Z z)⁻¹) := hf.2.1.inv_gaussian_exp hf.1.continuous
  exact ⟨hZ.1.log hp,hf.2.1.log_gaussian_exp hf.1.continuous,
    param_fderiv_log_growth Z id (hZ.1.differentiable (by norm_num)) hp hi hZ.2.1,
    param_second_log_growth Z id hZ.1 hp hi hZ.2.1 hZ.2.2⟩

theorem ParamRegular.gaussianStep {f : P × (E × ℝ) → ℝ} (hf : ParamRegular f) (m : ℝ) :
    ParamRegular (gaussianStep m (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2)))) := by
  change ParamRegular (fun z : P × E => if m = 0 then
    ∫ y, f (z.1,(z.2,y)) ∂gaussianReal 0 1 else
    Real.log (∫ y, Real.exp (m*f (z.1,(z.2,y))) ∂gaussianReal 0 1) / m)
  by_cases hm : m = 0
  · subst m
    simpa only [ite_true] using hf.gaussian_integral
  · have H := ((hf.const_mul m).log_gaussian_exp).const_mul m⁻¹
    simpa only [ite_eq_right hm,div_eq_mul_inv,mul_comm] using H
end ParameterRecursion
end SK.Analytic

end
end

end

end OAI
