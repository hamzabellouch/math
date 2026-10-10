import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.SliceExploration
import OAI.Probability.CriticalPercolation.Gluing.StripMoves
import OAI.Probability.CriticalPercolation.ProductMeasure.MeasurableSetRestrict

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def freshExitEvent (S : Set V) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | ∃ F : Finset E, N≤F.card ∧
    (F : Set E)⊆G.freshClusterBoundary (G.inducedEdges S) v ω∩ω}

lemma freshClusterBoundary_induced_mono {S : Set V} {v : V} (hv : v∈S)
    {ω η : Set E} (hωη : ω⊆η) :
    G.freshClusterBoundary (G.inducedEdges S) v ω ⊆
      G.freshClusterBoundary (G.inducedEdges S) v η := by
  rintro e ⟨⟨x,y,he,hx,hy⟩,heS⟩
  have hyS : y∈S := G.cluster_induced_subset ω S hv hy
  have hxS : x∉S := by
    intro hxS
    apply heS
    intro z hz
    rw [he] at hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact hxS
    · exact hyS
  refine ⟨⟨x,y,he,fun hx' => hxS (G.cluster_induced_subset η S hv hx'),?_⟩,heS⟩
  exact G.cluster_mono (Set.inter_subset_inter_left _ hωη) v hy

lemma freshExitEvent_upper {S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    IsUpperSet (G.freshExitEvent S v N) := by
  rintro ω η hωη ⟨F,hF,hFω⟩
  exact ⟨F,hF,fun e he =>
    ⟨G.freshClusterBoundary_induced_mono hv hωη (hFω he).1,hωη (hFω he).2⟩⟩

lemma freshExitEvent_finiteWitness {S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    BernoulliProduct.HasFiniteOpenWitness (G.freshExitEvent S v N) := by
  rintro ω ⟨F,hF,hFω⟩
  let X := G.inducedEdges S
  let C := G.cluster (ω∩X) v
  let T : Set V := (⋃ e∈(F : Set E), (↑(G.ends e).toFinset : Set V))∩C
  have hT : T.Finite :=
    (F.finite_toSet.biUnion (fun e _ => (G.ends e).toFinset.finite_toSet)).inter_of_left C
  obtain ⟨J,hJ,hJω,hconn⟩ := G.finite_subset_cluster_finite_witness hT Set.inter_subset_right
  have hsub : J∪(F : Set E)⊆ω := Set.union_subset
    (hJω.trans Set.inter_subset_left) (fun e he => (hFω he).2)
  refine ⟨J∪(F : Set E),hJ.union F.finite_toSet,hsub,F,hF,fun e he => ?_⟩
  obtain ⟨⟨x,y,hexy,_,hy⟩,heX⟩ := (hFω he).1
  have hyT : y∈T := by
    refine ⟨Set.mem_iUnion₂.mpr ⟨e,he,?_⟩,hy⟩
    have hm : y∈G.ends e := by rw [hexy]; simp
    simpa only [Finset.mem_coe,Sym2.mem_toFinset] using hm
  have hyJ : y∈G.cluster ((J∪(F : Set E))∩X) v :=
    G.cluster_mono (Set.subset_inter Set.subset_union_left
      (hJω.trans Set.inter_subset_right)) v (hconn hyT)
  have hx' : x∉G.cluster ((J∪(F : Set E))∩X) v := by
    intro hreach
    apply heX
    intro vertex hvertex
    rw [hexy] at hvertex
    rcases Sym2.mem_iff.mp hvertex with rfl | rfl
    · exact G.cluster_induced_subset (J∪(F : Set E)) S hv hreach
    · exact G.cluster_induced_subset ω S hv hy
  exact ⟨⟨⟨x,y,hexy,hx',hyJ⟩,heX⟩,Or.inr he⟩

lemma measurableSet_freshExitEvent [Countable E] {S : Set V} {v : V}
    (hv : v∈S) (N : ℕ) : MeasurableSet (G.freshExitEvent S v N) :=
  BernoulliProduct.measurableSet_finiteWitness _ (G.freshExitEvent_upper hv N)
    (G.freshExitEvent_finiteWitness hv N)

lemma freshExitEvent_of_card (S : Set V) (v : V) (N : ℕ) (ω : Set E)
    (hf : (G.freshClusterBoundary (G.inducedEdges S) v ω∩ω).Finite)
    (hN : N≤(G.freshClusterBoundary (G.inducedEdges S) v ω∩ω).ncard) :
    ω∈G.freshExitEvent S v N := by
  exact ⟨hf.toFinset,by rwa [← Set.ncard_eq_toFinset_card _ hf],
    fun e he => hf.mem_toFinset.mp he⟩

end CriticalPercolation.BondGraph
end
end

end OAI
