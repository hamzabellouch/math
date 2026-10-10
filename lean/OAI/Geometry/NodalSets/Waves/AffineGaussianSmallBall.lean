import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import OAI.Geometry.NodalSets.Waves.GaussianBoxBound

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma affine_gaussian_small_ball (L : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) (mean : ι → ℝ)
    (radius B : ℝ) (hr : 0 ≤ radius) (hB : 0 ≤ B) (hL : ‖L.symm.toContinuousLinearMap‖ ≤ B) :
    ((Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map (fun z ↦ mean+L z))
      {y | ‖y‖ ≤ radius} ≤
      ENNReal.ofReal ((2*(B*radius)/(Real.sqrt (2*Real.pi)))^(Fintype.card ι)) := by
  let center := L.symm (-mean)
  have hc : Continuous (fun z ↦ mean+L z) := continuous_const.add L.continuous
  rw [Measure.map_apply hc.measurable (isClosed_le continuous_norm continuous_const).measurableSet]
  have hsub : (fun z ↦ mean+L z) ⁻¹' {y | ‖y‖ ≤ radius} ⊆ {z | ‖z-center‖ ≤ B*radius} := by
    intro z hz
    have he : z-center = L.symm (mean+L z) := by simp [center,map_add,map_neg,add_comm]
    change ‖z-center‖ ≤ B*radius
    rw [he]
    apply (L.symm.toContinuousLinearMap.le_opNorm (mean+L z)).trans
    exact mul_le_mul hL hz (norm_nonneg _) hB
  apply le_trans (measure_mono hsub)
  simpa only [NNReal.coe_one,mul_one] using
    gaussian_coord_ball_bound (fun _ : ι ↦ 0) center (B*radius) (mul_nonneg hB hr) 1 one_ne_zero

end
end Yau.Probability

end OAI
