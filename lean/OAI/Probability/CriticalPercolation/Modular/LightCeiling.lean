import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.GraphGeometry.InducedCritical
import OAI.Probability.CriticalPercolation.Gluing.RelayMoves
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyNull
import OAI.Probability.CriticalPercolation.Modular.LightClusterNumber

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def modularDownSet (v : V) : Set V := {x | G.stabilizerWeight v x≤1}

lemma mem_modularDownSet_self (v : V) : v∈G.modularDownSet v := by
  simp [modularDownSet]

lemma cluster_eq_in_modularDownSet {ω : Set E} {v : V}
    (hv : G.clusterPeak ω v) :
    G.cluster (ω∩G.inducedEdges (G.modularDownSet v)) v=G.cluster ω v := by
  apply Set.Subset.antisymm (G.cluster_mono Set.inter_subset_left v)
  rintro x ⟨w⟩
  apply G.walk_reachable_induced _ ω w
  intro y hy
  exact hv y (w.takeUntil y hy).reachable

lemma lightInfiniteEvent_subset_some_lightInfinitePeak
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (o v : V) :
    G.lightInfiniteEvent o v⊆⋃ x : V, {ω | x∈G.lightInfinitePeaks ω} := by
  intro ω hω
  have hm : G.modularMass v (G.cluster ω v)≠∞ := by
    intro h
    exact hω.2.ne ((G.modularMass_eq_top_change_base hc hl o v _).mpr h)
  obtain ⟨x,hx,hpeak⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω v hm
  apply Set.mem_iUnion.mpr
  refine ⟨x,?_,hpeak⟩
  have hself : ω∈G.lightInfiniteEvent v v := by
    rwa [G.lightInfiniteEvent_change_base hc hl o v v] at hω
  exact G.lightInfiniteEvent_of_reachable hc hl hx hself

lemma exists_positive_lightInfinitePeak [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval) (o v : V)
    (hv : 0<G.law p (G.lightInfiniteEvent o v)) :
    ∃ x, 0<G.law p {ω | x∈G.lightInfinitePeaks ω} := by
  by_contra hn
  have hz : ∀ x, G.law p {ω | x∈G.lightInfinitePeaks ω}=0 := fun x =>
    le_antisymm (le_of_not_gt (fun h => hn ⟨x,h⟩)) bot_le
  exact hv.ne' (measure_mono_null (G.lightInfiniteEvent_subset_some_lightInfinitePeak hc hl o v)
    (measure_iUnion_null hz))

lemma peakInfinite_subset_induce_percolates (v : V) :
    {ω | (G.cluster ω v).Infinite ∧ G.clusterPeak ω v} ⊆
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set (G.inducedEdges (G.modularDownSet v)))) ⁻¹'
        (G.induce (G.modularDownSet v)).percolates := by
  rintro ω ⟨hi,hp⟩
  let v' : G.modularDownSet v := ⟨v,G.mem_modularDownSet_self v⟩
  refine ⟨v',?_⟩
  have he : Subtype.val '' (Subtype.val ⁻¹' ω : Set (G.inducedEdges (G.modularDownSet v)))=
      ω∩G.inducedEdges (G.modularDownSet v) := by
    ext e
    simp only [Set.mem_image,Set.mem_preimage,Set.mem_inter_iff]
    exact ⟨fun ⟨a,ha,he⟩ => he ▸ ⟨ha,a.property⟩,
      fun ⟨he,hS⟩ => ⟨⟨e,hS⟩,he,rfl⟩⟩
  apply Set.Infinite.of_image (f := Subtype.val)
  rw [G.induce_cluster_image,he]
  exact (G.cluster_eq_in_modularDownSet hp).symm ▸ hi

theorem positive_light_implies_downward_percolation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval) (o v : V)
    (hv : 0<G.law p (G.lightInfiniteEvent o v)) :
    ∃ x, 0<(G.induce (G.modularDownSet x)).law p (G.induce (G.modularDownSet x)).percolates := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨x,hx⟩ := G.exists_positive_lightInfinitePeak hc hl p o v hv
  refine ⟨x,?_⟩
  rw [←G.law_induce,Measure.map_apply]
  · apply hx.trans_le
    apply measure_mono
    intro ω hω
    exact G.peakInfinite_subset_induce_percolates x ⟨hω.1.1,hω.2⟩
  · exact Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  · exact (G.induce (G.modularDownSet x)).measurableSet_percolates

theorem nonunimodular_counterexample_downward_critical [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular)
    (o : V) (hp : G.law G.criticalProbability G.percolates≠0) :
    ∃ x, (G.induce (G.modularDownSet x)).criticalProbability=G.criticalProbability ∧
      0<(G.induce (G.modularDownSet x)).law
        (G.induce (G.modularDownSet x)).criticalProbability
        (G.induce (G.modularDownSet x)).percolates := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hmass := G.nonunimodular_critical_mass_finite_ae hc hl hq hpc hu o
  have hex : ∃ v, 0<G.law G.criticalProbability (G.lightInfiniteEvent o v) := by
    by_contra hn
    have hz : ∀ v, G.law G.criticalProbability (G.lightInfiniteEvent o v)=0 := fun v =>
      le_antisymm (le_of_not_gt (fun h => hn ⟨v,h⟩)) bot_le
    apply hp
    apply le_antisymm ?_ bot_le
    calc
      G.law G.criticalProbability G.percolates ≤
          G.law G.criticalProbability (⋃ v, G.lightInfiniteEvent o v) := by
        apply measure_mono_ae
        filter_upwards [hmass] with ω hω
        intro ⟨v,hv⟩
        exact Set.mem_iUnion.mpr ⟨v,hv,hω v⟩
      _ = 0 := measure_iUnion_null hz
  obtain ⟨v,hv⟩ := hex
  obtain ⟨x,hx⟩ := G.positive_light_implies_downward_percolation hc hl _ o v hv
  have he := G.induce_criticalProbability_eq_of_pos (G.modularDownSet x) hx
  exact ⟨x,he,by rwa [he]⟩

end CriticalPercolation.BondGraph
end
end

end OAI
