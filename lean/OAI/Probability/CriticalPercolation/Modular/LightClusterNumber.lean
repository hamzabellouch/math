import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Clusters.GraphErgodicity
import OAI.Probability.CriticalPercolation.Criticality.InvariantFiniteSets
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.ModularSuperlevels

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma lightInfiniteEvent_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a v : V) : G.lightInfiniteEvent o v=G.lightInfiniteEvent a v := by
  ext ω
  change (_ ∧ _<∞) ↔ (_ ∧ _<∞)
  simp only [lt_top_iff_ne_top]
  exact and_congr Iff.rfl (not_congr (G.modularMass_eq_top_change_base hc hl o a _))

lemma lightInfiniteEvent_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {ω : Set E} {v x : V} (hx : (G.openGraph ω).Reachable v x)
    (hv : ω∈G.lightInfiniteEvent v v) : ω∈G.lightInfiniteEvent x x := by
  change (G.cluster ω x).Infinite ∧ G.modularMass x (G.cluster ω x)<∞
  have he := G.cluster_eq_of_reachable hx
  rw [←he]
  refine ⟨hv.1,?_⟩
  rw [lt_top_iff_ne_top]
  intro h
  exact hv.2.ne ((G.modularMass_eq_top_change_base hc hl v x _).mpr h)

lemma Aut.lightInfiniteEvent_self_iff (φ : G.Aut) (ω : Set E) (v : V) :
    φ.edge '' ω∈G.lightInfiniteEvent (φ.vertex v) (φ.vertex v) ↔
      ω∈G.lightInfiniteEvent v v := by
  change (_ ∧ _<∞) ↔ (_ ∧ _<∞)
  rw [←φ.cluster_image,φ.modularMass_image]
  exact and_congr (Set.infinite_image_iff φ.vertex.injective.injOn) Iff.rfl

def lightInfinitePeaks (ω : Set E) : Set V :=
  {v | ω∈G.lightInfiniteEvent v v ∧ G.clusterPeak ω v}

def lightClusterCover (ω : Set E) (S : Set V) : Prop :=
  ∀ v, ω∈G.lightInfiniteEvent v v → ∃ s∈S, (G.openGraph ω).Reachable v s

def infinitelyManyLightClusters (ω : Set E) : Prop :=
  ∀ S : Finset V, ∃ v, ω∈G.lightInfiniteEvent v v ∧
    ∀ s∈S, ¬(G.openGraph ω).Reachable v s

lemma measurable_lightInfinitePeaks [Countable V] [Countable E] (v : V) :
    Measurable (fun ω => v∈G.lightInfinitePeaks ω) :=
  (G.measurableSet_lightInfiniteEvent v v).mem.and (G.measurable_clusterPeak v)

lemma lightInfinitePeaks_aut (φ : G.Aut) (ω : Set E) :
    G.lightInfinitePeaks (φ.edge '' ω)=φ.vertex '' G.lightInfinitePeaks ω := by
  ext y
  obtain ⟨v,rfl⟩ := φ.vertex.surjective y
  simp only [lightInfinitePeaks,Set.mem_ofPred_eq,φ.lightInfiniteEvent_self_iff,
    φ.clusterPeak_iff,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma lightInfinitePeaks_finite_of_cover (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (S : Set V) (hS : S.Finite) (hcover : G.lightClusterCover ω S) :
    (G.lightInfinitePeaks ω).Finite := by
  let T := {s∈S | ω∈G.lightInfiniteEvent s s}
  have hT : T.Finite := hS.subset (fun _ hx => hx.1)
  refine (hT.biUnion (fun s hs => G.clusterPeaks_finite_of_mass_ne_top hc hl ω s hs.2.2.ne)).subset ?_
  intro v hv
  obtain ⟨s,hs,hvs⟩ := hcover v hv.1
  exact Set.mem_iUnion₂.mpr ⟨s,⟨hs,G.lightInfiniteEvent_of_reachable hc hl hvs hv.1⟩,hvs.symm,hv.2⟩

lemma lightInfinitePeaks_nonempty (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hv : ω∈G.lightInfiniteEvent v v) :
    (G.lightInfinitePeaks ω).Nonempty := by
  obtain ⟨x,hx,hpeak⟩ := G.clusterPeaks_nonempty_of_mass_ne_top hc hl ω v hv.2.ne
  exact ⟨x,G.lightInfiniteEvent_of_reachable hc hl hx hv,hpeak⟩

lemma infinitelyManyLightClusters_iff_no_finite_cover (ω : Set E) :
    G.infinitelyManyLightClusters ω ↔ ∀ S : Finset V, ¬G.lightClusterCover ω (S : Set V) := by
  simp only [infinitelyManyLightClusters,lightClusterCover]
  push Not
  rfl

lemma measurable_infinitelyManyLightClusters [Countable V] [Countable E] :
    Measurable G.infinitelyManyLightClusters := by
  exact .forall fun S : Finset V => .exists fun v =>
    (G.measurableSet_lightInfiniteEvent v v).mem.and
      (.forall fun s => .imp measurable_const (G.measurable_reachable v s).not)

theorem light_zero_or_infinitely_many_ae [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, (∃ v, ω∈G.lightInfiniteEvent v v) → G.infinitelyManyLightClusters ω := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hh := G.invariant_finite_vertex_set_empty_ae hc hl hq p G.lightInfinitePeaks
    G.measurable_lightInfinitePeaks G.lightInfinitePeaks_aut
  filter_upwards [hh] with ω hω ⟨v,hv⟩
  rw [G.infinitelyManyLightClusters_iff_no_finite_cover]
  intro S hS
  have hf := G.lightInfinitePeaks_finite_of_cover hc hl ω (S : Set V) S.finite_toSet hS
  have hn := G.lightInfinitePeaks_nonempty hc hl ω v hv
  rw [hω hf] at hn
  exact Set.not_nonempty_empty hn

lemma light_exists_invariant (φ : G.Aut) (ω : Set E) :
    (∃ v, φ.edge '' ω∈G.lightInfiniteEvent v v) ↔ ∃ v, ω∈G.lightInfiniteEvent v v := by
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨x,rfl⟩ := φ.vertex.surjective v
    exact ⟨x,(φ.lightInfiniteEvent_self_iff G ω x).mp hv⟩
  · rintro ⟨v,hv⟩
    exact ⟨φ.vertex v,(φ.lightInfiniteEvent_self_iff G ω v).mpr hv⟩

theorem infinitely_many_light_ae_of_positive [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (o v : V) (hv : 0<G.law p (G.lightInfiniteEvent o v)) :
    ∀ᵐ ω ∂G.law p, G.infinitelyManyLightClusters ω := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hm : MeasurableSet {ω | ∃ v, ω∈G.lightInfiniteEvent v v} :=
    (Measurable.exists fun v => (G.measurableSet_lightInfiniteEvent v v).mem).setOf
  have hpos : 0<G.law p {ω | ∃ v, ω∈G.lightInfiniteEvent v v} := by
    apply hv.trans_le
    apply measure_mono
    intro ω hω
    refine ⟨v,?_⟩
    rwa [G.lightInfiniteEvent_change_base hc hl o v v] at hω
  have hone : G.law p {ω | ∃ v, ω∈G.lightInfiniteEvent v v}=1 := by
    rcases G.invariant_event_zero_one hc hl hq p _ hm
      (fun φ => Set.ext fun ω => G.light_exists_invariant φ ω) with hz|ho
    · exact False.elim (hpos.ne' hz)
    · exact ho
  have hex : ∀ᵐ ω ∂G.law p, ∃ v, ω∈G.lightInfiniteEvent v v := by
    exact (ae_iff_prob_eq_one hm.mem).mpr hone
  filter_upwards [G.light_zero_or_infinitely_many_ae hc hl hq p,hex] with ω hω hh
  exact hω hh

end CriticalPercolation.BondGraph
end
end

end OAI
