import OAI.GroupTheory.PolycyclicRecognition.Analysis.SeparatedTupleVolume
import Mathlib.Topology.Compactness.LocallyCompact

namespace OAI

/-! # A positive compact thickening for finite factor tuples -/

noncomputable section
namespace PolycyclicRecognition

open Set MeasureTheory
open scoped Topology

/-- Continuity of factor multiplication supplies the positive compact cell
used to turn separated tuples into Haar volume. -/
theorem exists_small_factor_tuple_neighborhood
    {N D G : Type*} [Group N] [Group D] [Group G]
    [TopologicalSpace N] [TopologicalSpace D]
    [LocallyCompactSpace N] [LocallyCompactSpace D]
    [MeasurableSpace N] [MeasurableSpace D] [BorelSpace N] [BorelSpace D]
    [MetricSpace G] [IsTopologicalGroup G]
    (ι : N →* G) (κ : D →* G) (hι : Continuous ι) (hκ : Continuous κ)
    (μ : Measure N) (ν : Measure D) [SigmaFinite μ] [SigmaFinite ν]
    [μ.IsOpenPosMeasure] [ν.IsOpenPosMeasure]
    (h : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ U : Set ((Fin h → N) × (Fin h → D)), IsCompact U ∧
      ((Measure.pi fun _ : Fin h => μ).prod (Measure.pi fun _ : Fin h => ν)) U ≠ 0 ∧
      ∀ z ∈ U, dist (1 : Fin h → G) (fun i => ι (z.1 i) * κ (z.2 i)) < ρ / 2 := by
  let q : ((Fin h → N) × (Fin h → D)) → (Fin h → G) :=
    fun z i => ι (z.1 i) * κ (z.2 i)
  have hq : Continuous q := continuous_pi (fun i =>
    (hι.comp ((continuous_apply i).comp continuous_fst)).mul
      (hκ.comp ((continuous_apply i).comp continuous_snd)))
  have hopen : IsOpen {z | dist (1 : Fin h → G) (q z) < ρ / 2} :=
    isOpen_lt (continuous_const.dist hq) continuous_const
  have h1 : (1, 1) ∈ {z | dist (1 : Fin h → G) (q z) < ρ / 2} := by
    have he : q (1, 1) = 1 := by ext i; simp [q]
    simpa only [mem_ofPred_eq, he, dist_self] using half_pos hρ
  obtain ⟨U, hU, hU1, hsmall⟩ := exists_compact_subset hopen h1
  refine ⟨U, hU, ?_, hsmall⟩
  exact (Measure.measure_pos_of_nonempty_interior _ ⟨(1, 1), hU1⟩).ne'

end PolycyclicRecognition

end

end OAI
