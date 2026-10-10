import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarAverageCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarGradient_comp_fderiv {f : ℝ → ℝ} (hf : BoundedDerivs f) (L : E →L[ℝ] ℝ) (z : E) :
    fderiv ℝ (fun z => rootGradient 0 f (L z)) z=rootHessian 0 f (L z) • L := by
  have hd (y : ℝ) : HasDerivAt (rootGradient 0 f) (rootHessian 0 f y) y := by
    simpa only [parameterAxis,smul_eq_mul,mul_one,zero_add] using rootGradientLine_hasDerivAt 0 hf 0 y
  have H := ((hd (L z)).hasFDerivAt (𝕜 := ℝ)).comp z L.hasFDerivAt
  change HasFDerivAt (fun z => rootGradient 0 f (L z)) _ z at H
  have H := H.fderiv
  rw [H]
  ext u
  simp only [ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul]
  ring

theorem scalarGradient_comp_regular {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (L : E →L[ℝ] ℝ) :
    ContDiff ℝ 1 (fun z => rootGradient 0 f (L z)) ∧
    HasExpGrowth (fun z => rootGradient 0 f (L z)) ∧
    HasExpGrowth (fderiv ℝ (fun z => rootGradient 0 f (L z))) := by
  have hc : ContDiff ℝ 1 (rootGradient 0 f) := directionalGradient_contDiff f hf.1 (parameterAxis 0)
  refine ⟨hc.comp L.contDiff,HasExpGrowth.of_bounded zero_le_one (fun z => ?_),?_⟩
  · simpa only [Real.norm_eq_abs] using (hspin.bounds (L z)).1
  · apply HasExpGrowth.of_bounded (norm_nonneg L)
    intro z
    rw [scalarGradient_comp_fderiv hf L z,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (hspin.bounds (L z)).2 (norm_nonneg L)).trans_eq (one_mul _)

end SK.Analytic

end
end

end OAI
