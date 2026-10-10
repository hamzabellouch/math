import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterGrowth

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterComposition
variable {P E X Y : Type} [NormedAddCommGroup P] [NormedAddCommGroup E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem param_fderiv_compCLM_growth (f : Y → ℝ) (L : X →L[ℝ] Y) (ι : P × E → X)
    (hf : Differentiable ℝ f)
    (h : ParamExpGrowth (fun z => fderiv ℝ f (L (ι z)))) :
    ParamExpGrowth (fun z => fderiv ℝ (fun x => f (L x)) (ι z)) := by
  apply h.of_norm_le (norm_nonneg L)
  intro z
  have he : fderiv ℝ (fun x => f (L x)) (ι z) = (fderiv ℝ f (L (ι z))).comp L :=
    ((hf (L (ι z))).hasFDerivAt.comp (ι z) L.hasFDerivAt).fderiv
  rw [he]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

theorem param_second_compCLM_growth (f : Y → ℝ) (L : X →L[ℝ] Y) (ι : P × E → X)
    (hf : ContDiff ℝ 2 f)
    (h : ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ f) (L (ι z)))) :
    ParamExpGrowth (fun z => fderiv ℝ (fderiv ℝ (fun x => f (L x))) (ι z)) := by
  let A : (Y →L[ℝ] ℝ) →L[ℝ] X →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ X Y ℝ).flip L
  have hA (B : Y →L[ℝ] ℝ) : A B = B.comp L := rfl
  have hAn : ‖A‖ ≤ ‖L‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro B
    rw [hA]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)
  have hd := hf.differentiable (by norm_num)
  have hdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun x => f (L x)) = fun x => A (fderiv ℝ f (L x)) := by
    funext x
    exact ((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv
  apply h.of_norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg L))
  intro z
  have hsec := A.hasFDerivAt.comp (ι z)
    ((hdd (L (ι z))).hasFDerivAt.comp (ι z) L.hasFDerivAt)
  change HasFDerivAt (fun x => A (fderiv ℝ f (L x)))
    (A.comp ((fderiv ℝ (fderiv ℝ f) (L (ι z))).comp L)) (ι z) at hsec
  rw [heq,hsec.fderiv]
  calc
    _ ≤ ‖A‖*‖(fderiv ℝ (fderiv ℝ f) (L (ι z))).comp L‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖*(‖fderiv ℝ (fderiv ℝ f) (L (ι z))‖*‖L‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring
end ParameterComposition
end SK.Analytic

end
end

end

end OAI
