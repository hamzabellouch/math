import OAI.GroupTheory.PolycyclicRecognition.Analysis.MidpointStepPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSegmentLimit

namespace OAI

/-! # Minimizing segments from properness and approximate midpoints -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology

theorem exists_metric_segment {X : Type*} [MetricSpace X] [ProperSpace X]
    (hmid : HasApproximateMidpoints X) (x y : X) :
    ∃ γ : ℝ → X, γ 0 = x ∧ γ 1 = y ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) ≤ dist x y * |s - t| := by
  let h : HasMetricMidpoints X := exists_midpoint_of_proper hmid
  apply exists_segment_of_compact_approximations x y (midpointStepPath h x y)
    (fun n => dist x y / (2 : ℝ) ^ n)
  · exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_div_atTop _
  · exact midpointStepPath_zero h x y
  · exact midpointStepPath_one h x y
  · exact midpointStepPath_ball h x y
  · exact midpointStepPath_dist h x y

end PolycyclicRecognition

end

end OAI
