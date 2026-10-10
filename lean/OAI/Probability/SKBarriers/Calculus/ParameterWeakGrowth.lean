import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterGrowth

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterWeakGrowth
variable {P E F : Type} [NormedAddCommGroup P] [NormedAddCommGroup E] [Norm F]

theorem ParamExpGrowth.weakNorm {f : P × E → F} (hf : ParamExpGrowth f)
    (hn : ∀ z, 0 ≤ ‖f z‖) : ParamExpGrowth (fun z => ‖f z‖) := by
  apply hf.of_norm_le zero_le_one
  intro z
  rw [Real.norm_eq_abs,abs_of_nonneg (hn z),one_mul]

theorem ParamExpGrowth.weakLocallyDominated {f : P × (E × ℝ) → F}
    (hf : ParamExpGrowth f) :
    GaussianLocallyDominated (fun z : (P × E) × ℝ => f (z.1.1,(z.1.2,z.2))) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨fun y => C*Real.exp (M*R)*Real.exp (M*|y|),
    (integrable_exp_mul_abs_gaussian M).const_mul _,?_⟩
  rintro ⟨p,e⟩ y hpe
  have hp : ‖p‖ ≤ R := (le_max_left _ _).trans hpe
  have he : ‖e‖ ≤ R := (le_max_right _ _).trans hpe
  apply (hf p (e,y) hp).trans
  change C*Real.exp (M*‖(e,y)‖) ≤ C*Real.exp (M*R)*Real.exp (M*|y|)
  rw [mul_assoc,← Real.exp_add,← mul_add]
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Prod.norm_def,Real.norm_eq_abs]
  exact max_le (he.trans (le_add_of_nonneg_right (abs_nonneg _)))
    (le_add_of_nonneg_left ((norm_nonneg e).trans he))
end ParameterWeakGrowth
end SK.Analytic

end
end

end

end OAI
