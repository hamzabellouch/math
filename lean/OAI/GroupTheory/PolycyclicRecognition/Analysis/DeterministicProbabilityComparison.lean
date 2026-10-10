import OAI.GroupTheory.PolycyclicRecognition.Analysis.ThreeProbeConcentration

namespace OAI

/-! # Deterministic affine comparisons extracted from probable comparisons -/

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A constant event cannot have vanishing positive probability unless
its deterministic error tends to zero. -/
theorem deterministic_distance_tendsto_zero_of_probability
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (a b : ℕ → Y)
    (hp : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {_x | ε ≤ dist (a n) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := (hp ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [hh] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
  by_contra h
  have he : {x : X | ε ≤ dist (a n) (b n)} = univ := by
    ext x
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact le_of_not_gt h
  rw [he, measure_univ] at hn
  exact (lt_irrefl (1 : ℝ≥0∞)) hn

/-- Two deterministic approximants agree asymptotically when their
sampled profiles can be compared on a common probability law. -/
theorem deterministic_distance_tendsto_zero_of_coupled_profiles
    {X Y : Type*} [MeasurableSpace X] [PseudoMetricSpace Y]
    (μ : ℕ → ProbabilityMeasure X) (a b : ℕ → Y) (f g : ℕ → X → Y)
    (hleft : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (a n) (f n x)}) atTop (𝓝 0))
    (hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (f n x) (g n x)}) atTop (𝓝 0))
    (hright : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (μ n : Measure X) {x | ε ≤ dist (g n x) (b n)}) atTop (𝓝 0)) :
    Tendsto (fun n => dist (a n) (b n)) atTop (𝓝 0) := by
  apply deterministic_distance_tendsto_zero_of_probability μ a b
  intro ε hε
  apply bad_distance_triangle_tendsto_zero (fun n => (μ n : Measure X))
    (fun n _ => a n) g (fun n _ => b n) _ hright ε hε
  exact fun η hη => bad_distance_triangle_tendsto_zero (fun n => (μ n : Measure X))
    (fun n _ => a n) f g hleft hpair η hη

end PolycyclicRecognition

end OAI
