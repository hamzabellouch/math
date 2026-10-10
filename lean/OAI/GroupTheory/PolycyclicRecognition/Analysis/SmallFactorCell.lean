import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactTupleThickening
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-! # A fixed small factor cell for varying Haar normalizations -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped Topology

/-- This cell is chosen before the Haar normalization used by a probe region.
Its interior contains the identity, so every product Haar measure gives it
positive finite mass. -/
theorem exists_small_factor_cell
    {N D G : Type*} [Group N] [Group D] [Group G]
    [TopologicalSpace N] [TopologicalSpace D]
    [LocallyCompactSpace N] [LocallyCompactSpace D]
    [MetricSpace G] [IsTopologicalGroup G]
    (ι : N →* G) (κ : D →* G) (hι : Continuous ι) (hκ : Continuous κ) :
    ∃ U : Set (N × D), IsCompact U ∧ (1 : N × D) ∈ interior U ∧
      ∀ z ∈ U, dist (1 : G) (ι z.1 * κ z.2) < 1 / 2 := by
  have hopen : IsOpen {z : N × D | dist (1 : G) (ι z.1 * κ z.2) < 1 / 2} :=
    isOpen_lt (continuous_const.dist
      ((hι.comp continuous_fst).mul (hκ.comp continuous_snd))) continuous_const
  have hone : (1 : N × D) ∈ {z : N × D | dist (1 : G) (ι z.1 * κ z.2) < 1 / 2} := by
    simp
  exact exists_compact_subset hopen hone

/-- The same fixed cell works for each of the section-dependent Haar
products appearing in the target comparison. -/
theorem small_factor_cell_measure
    {N D : Type*} [TopologicalSpace N] [TopologicalSpace D]
    [T2Space N] [T2Space D]
    [SecondCountableTopology N] [SecondCountableTopology D]
    [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
    (μ : Measure N) (ν : Measure D) [SFinite μ] [SFinite ν]
    [μ.IsOpenPosMeasure] [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {U : Set (N × D)} (hU : IsCompact U) (hne : (interior U).Nonempty) :
    MeasurableSet U ∧ (μ.prod ν) U ≠ 0 ∧ (μ.prod ν) U ≠ ⊤ := by
  exact ⟨hU.isClosed.measurableSet,
    (Measure.measure_pos_of_nonempty_interior _ hne).ne', hU.measure_ne_top⟩

end PolycyclicRecognition

end

end OAI
