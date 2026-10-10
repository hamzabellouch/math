import Mathlib

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Filter Topology

variable {X : Type*} [MeasurableSpace X] [MetricSpace X]
  [OpensMeasurableSpace X] [Nonempty X]

theorem finiteMeasure_cell_mass_tendsto (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (s : Set X) (hboundary : (ν : Measure X) (frontier s) = 0) :
    Tendsto (fun j => (μ j : Measure X).real s) atTop (𝓝 ((ν : Measure X).real s)) := by
  have hn : Tendsto (fun j => (μ j).normalize) atTop (𝓝 ν.normalize) :=
    FiniteMeasure.tendsto_normalize_of_tendsto hweak hν
  have hb : ν.normalize (frontier s) = 0 := by
    rw [ν.normalize_eq_of_nonzero hν]
    rw [(ν.null_iff_toMeasure_null _).mpr hboundary, mul_zero]
  have hp := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hb
  have hmass : Tendsto (fun j => (μ j) s) atTop (𝓝 (ν s)) := by
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using! hweak.mass.mul hp
  exact NNReal.continuous_coe.continuousAt.tendsto.comp hmass

omit [OpensMeasurableSpace X] [Nonempty X] in
theorem null_frontier_inter (ν : Measure X) (s t : Set X)
    (hs : ν (frontier s) = 0) (ht : ν (frontier t) = 0) :
    ν (frontier (s ∩ t)) = 0 :=
  measure_mono_null (frontier_inter_subset s t)
    (measure_union_null (measure_mono_null inter_subset_left hs)
      (measure_mono_null inter_subset_right ht))

theorem finiteMeasure_cell_intersection_mass_tendsto
    (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hweak : Tendsto μ atTop (𝓝 ν)) (hν : ν ≠ 0)
    (s t : Set X) (hs : (ν : Measure X) (frontier s) = 0)
    (ht : (ν : Measure X) (frontier t) = 0) :
    Tendsto (fun j => (μ j : Measure X).real (s ∩ t)) atTop
      (𝓝 ((ν : Measure X).real (s ∩ t))) :=
  finiteMeasure_cell_mass_tendsto μ ν hweak hν (s ∩ t) (null_frontier_inter _ s t hs ht)

end

end RieszRectifiability

end OAI
