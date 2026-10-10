import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterSmooth

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
section ParameterBilinear
variable {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ParamExpGrowth.continuousLinearMap (L : P × E →L[ℝ] F) : ParamExpGrowth (fun z => L z) := by
  intro R
  refine ⟨‖L‖*Real.exp (max R 0),1,by positivity,by norm_num,?_⟩
  intro p e hp
  calc
    ‖L (p,e)‖ ≤ ‖L‖*‖(p,e)‖ := L.le_opNorm _
    _ ≤ ‖L‖*Real.exp (‖(p,e)‖) := by
      gcongr
      have hh := Real.add_one_le_exp ‖(p,e)‖
      linarith
    _ ≤ ‖L‖*Real.exp (max R 0+‖e‖) := by
      gcongr
      rw [Prod.norm_def]
      exact max_le ((hp.trans (le_max_left _ _)).trans (le_add_of_nonneg_right (norm_nonneg e)))
        (le_add_of_nonneg_left (le_max_right _ _))
    _ = _ := by rw [Real.exp_add,one_mul,mul_assoc]

theorem paramRegular_bilinear (B : P →L[ℝ] E →L[ℝ] ℝ) :
    ParamRegular (fun z : P × E => B z.1 z.2) := by
  have hc : ContDiff ℝ 2 (fun z : P × E => B z.1 z.2) := B.isBoundedBilinearMap.contDiff
  have he : fderiv ℝ (fun z : P × E => B z.1 z.2) = fun z => B.deriv₂ z := by
    funext z
    rw [B.isBoundedBilinearMap.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    rfl
  refine ⟨hc,?_,?_,?_⟩
  · intro R
    refine ⟨‖B‖*max R 0,by positivity,?_⟩
    intro p e hp
    calc
      |B p e| = ‖B p e‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖B p‖*‖e‖ := (B p).le_opNorm e
      _ ≤ (‖B‖*‖p‖)*‖e‖ := mul_le_mul_of_nonneg_right (B.le_opNorm p) (norm_nonneg e)
      _ ≤ (‖B‖*max R 0)*(1+‖e‖) := by
        gcongr
        · exact hp.trans (le_max_left _ _)
        · linarith
  · rw [he]
    exact ParamExpGrowth.continuousLinearMap B.deriv₂
  · rw [he]
    intro R
    refine ⟨‖B.deriv₂‖,0,ContinuousLinearMap.opNorm_nonneg _,le_rfl,?_⟩
    intro p e _
    rw [B.deriv₂.fderiv]
    simp only [zero_mul,Real.exp_zero,mul_one]
    exact le_rfl
end ParameterBilinear
end SK.Analytic

end
end

end

end OAI
