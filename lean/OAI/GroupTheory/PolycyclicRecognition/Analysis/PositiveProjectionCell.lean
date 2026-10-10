import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Basic

namespace OAI

/-! # Positive compact cells with small projections -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Metric Set

/-- A continuous projection admits a compact cell of positive finite mass
whose entire projection stays in a prescribed ball. -/
theorem exists_compact_positive_projection_cell
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [PseudoMetricSpace Y]
    (μ : Measure X) [IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]
    (q : X → Y) (hq : Continuous q) (x₀ : X) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ U : Set X, IsCompact U ∧ MeasurableSet U ∧ 0 < μ U ∧ μ U < ⊤ ∧
      ∀ x ∈ U, dist (q x₀) (q x) < ρ := by
  obtain ⟨U, hU, h₀, hsub⟩ := exists_compact_subset
    (isOpen_ball.preimage hq) (show x₀ ∈ q ⁻¹' ball (q x₀) ρ by simpa using hρ)
  refine ⟨U, hU, hU.isClosed.measurableSet,
    measure_pos_of_nonempty_interior μ ⟨x₀, h₀⟩, hU.measure_lt_top, ?_⟩
  intro x hx
  simpa only [Set.mem_preimage, mem_ball, dist_comm] using hsub hx

end PolycyclicRecognition

end

end OAI
