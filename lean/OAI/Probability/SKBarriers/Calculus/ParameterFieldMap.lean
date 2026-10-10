import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterAlgebra

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterFieldMap
variable {P E D : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D]

omit [NormedSpace ℝ P] in
theorem ParamExpGrowth.fieldComp {F : Type} [Norm F] {f : P × E → F}
    (hf : ParamExpGrowth f) (L : D →L[ℝ] E) :
    ParamExpGrowth (fun z : P × D => f (z.1,L z.2)) := by
  intro R
  obtain ⟨C,M,hC,hM,hf⟩ := hf R
  refine ⟨C,M*‖L‖,hC,mul_nonneg hM (norm_nonneg L),?_⟩
  intro p e hp
  apply (hf p (L e) hp).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.2
  exact (mul_le_mul_of_nonneg_left (L.le_opNorm e) hM).trans_eq (mul_assoc _ _ _).symm

omit [NormedSpace ℝ P] in
theorem ParamLinearGrowth.fieldComp {f : P × E → ℝ}
    (hf : ParamLinearGrowth f) (L : D →L[ℝ] E) :
    ParamLinearGrowth (fun z : P × D => f (z.1,L z.2)) := by
  intro R
  obtain ⟨C,hC,hf⟩ := hf R
  refine ⟨C*(1+‖L‖),mul_nonneg hC (by positivity),?_⟩
  intro p e hp
  calc
    _ ≤ C*(1+‖L e‖) := hf p (L e) hp
    _ ≤ C*((1+‖L‖)*(1+‖e‖)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith [L.le_opNorm e,norm_nonneg L,norm_nonneg e]
    _ = _ := by ring

theorem ParamSmooth.fieldComp {f : P × E → ℝ} (hf : ParamSmooth f) (L : D →L[ℝ] E) :
    ParamSmooth (fun z : P × D => f (z.1,L z.2)) := by
  let A : P × D →L[ℝ] P × E := (ContinuousLinearMap.id ℝ P).prodMap L
  exact ⟨hf.1.comp A.contDiff,hf.2.1.fieldComp L,
    param_fderiv_compCLM_growth f A id (hf.1.differentiable (by norm_num))
      (hf.2.2.1.fieldComp L),
    param_second_compCLM_growth f A id hf.1 (hf.2.2.2.fieldComp L)⟩

theorem ParamRegular.fieldComp {f : P × E → ℝ} (hf : ParamRegular f) (L : D →L[ℝ] E) :
    ParamRegular (fun z : P × D => f (z.1,L z.2)) := by
  have h := hf.toSmooth.fieldComp L
  exact ⟨h.1,hf.2.1.fieldComp L,h.2.2⟩
end ParameterFieldMap
end SK.Analytic

end
end

end

end OAI
