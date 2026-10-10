import OAI.GroupTheory.PolycyclicRecognition.Analysis.InvariantMetrization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedMetricChains

namespace OAI

/-! # Constructing the proper chain metric used in model comparison -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric Filter Topology
open scoped Pointwise

/-- Enlarge compact generators by a compact identity neighborhood and inverses. -/
theorem exists_compact_symmetric_generating_neighborhood
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {L : Set G} (hL : IsCompact L)
    (hgen : Subgroup.closure L = ⊤) :
    ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 (1 : G) ∧
      Subgroup.closure K = ⊤ ∧ ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K := by
  obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds (1 : G)
  let Q := L ∪ U
  let K := Q ∪ Q⁻¹
  have hQ : IsCompact Q := hL.union hU
  refine ⟨K, hQ.union hQ.inv, ?_, ?_, ?_⟩
  · exact mem_of_superset hUn (by intro x hx; exact Or.inl (Or.inr hx))
  · apply top_unique
    rw [← hgen]
    exact Subgroup.closure_mono (by intro x hx; exact Or.inl (Or.inl hx))
  · intro g
    simp only [K, Set.mem_union, Set.mem_inv, inv_inv]
    exact or_comm

/-- Specialization of the proper chain-metric construction to the exact
compact-generation input used by the recognition theorem. -/
theorem geodesicMetricExistenceInput : GeodesicMetricExistenceInput := by
  intro G _ _ _ _ _ _ hgen
  obtain ⟨m, hm, hiso, hbound⟩ := exists_bounded_leftInvariant_metric (H := G)
  let mc : MetricSpace G := m.replaceTopology hm.symm
  have hmc : mc = m := m.replaceTopology_eq hm.symm
  let := mc
  have hi : IsIsometricSMul G G :=
    Eq.mp (congrArg (fun d : MetricSpace G => letI := d; IsIsometricSMul G G) hmc.symm) hiso
  let := hi
  have hb : ∀ x y : G, dist x y ≤ 1 :=
    Eq.mp (congrArg (fun d : MetricSpace G => letI := d; ∀ x y : G, dist x y ≤ 1) hmc.symm) hbound
  obtain ⟨L, hL, hLgen⟩ := hgen
  obtain ⟨K, hK, hKn, hKgen, hKsymm⟩ :=
    exists_compact_symmetric_generating_neighborhood hL hLgen
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp hKn
  let δ := min 1 (ε / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hε)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hball : ∀ g : G, dist 1 g ≤ δ → g ∈ K := by
    intro g hg
    apply hεK
    change dist g 1 < ε
    rw [dist_comm]
    exact hg.trans_lt ((min_le_right 1 (ε / 2)).trans_lt (half_lt_self hε))
  exact ⟨weightedProperChainMetric K hKgen hKsymm hb δ hδ hδ1 hball hK⟩

end PolycyclicRecognition

end

end OAI
