import OAI.MathematicalPhysics.CriticalSK.FunctionalMeasurability
import OAI.MathematicalPhysics.CriticalSK.MixingMeasurability

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

theorem critical_logSobolev_lower_bound (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (2 / 3 - δ) ≤ logSobolevConstant W}) atTop (𝓝 1) := by
  have hp := critical_relaxation_lower_bound δ hδ
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [(tendsto_order.mp hp).1 a ha, eventually_gt_atTop 0] with n hn hnpos
    refine lt_of_lt_of_le hn (measureReal_mono ?_)
    intro W hW
    exact hW.trans (relaxationTime_le_logSobolevConstant W hnpos)
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

theorem critical_lower_exponents
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (2 / 3 - δ) ≤ continuousMixingAt W ε}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (5 / 3 - δ) ≤ (discreteMixingAt W ε : ℝ)}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (2 / 3 - δ) ≤ relaxationTime W}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real
      {W | (n : ℝ) ^ (2 / 3 - δ) ≤ logSobolevConstant W}) atTop (𝓝 1) := by
  have hm := critical_mixing_lower_bounds_at ε hε hεhalf δ hδ
  exact ⟨hm.1, hm.2, critical_relaxation_lower_bound δ hδ,
    critical_logSobolev_lower_bound δ hδ⟩

end CriticalSK
end

end OAI
