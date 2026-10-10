import OAI.Combinatorics.ThinTrees.PartitionHierarchy

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

def thresholdEdges (_G : MultiGraph n m) (R : Fin m → ℝ) (s : ℝ) : Finset (Fin m) := univ.filter (fun e => R e ≤ s)
def rankedEdges (R : Fin m → ℝ) (i : ℕ) : Finset (Fin m) := univ.filter (fun e => (G.thresholdEdges R (R e)).card ≤ i)
lemma rankedEdges_mono (R : Fin m → ℝ) : Monotone (G.rankedEdges R) := by
  intro i j hij e he
  exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2.trans hij⟩
lemma rankedEdges_full (R : Fin m → ℝ) : G.rankedEdges R m=univ := by
  ext e
  simp only [rankedEdges,mem_filter,mem_univ,true_and,iff_true]
  exact (card_le_card (subset_univ _)).trans_eq (by simp)
lemma rankedEdges_threshold (R : Fin m → ℝ) (s : ℝ) :
    G.rankedEdges R (G.thresholdEdges R s).card=G.thresholdEdges R s := by
  ext e
  change (e ∈ univ.filter (fun f => (univ.filter (fun g => R g ≤ R f)).card ≤ (univ.filter (fun g => R g ≤ s)).card)) ↔ e ∈ univ.filter (fun f => R f ≤ s)
  simp only [mem_filter,mem_univ,true_and]
  constructor
  · intro h
    by_contra he
    have hlt : s < R e := lt_of_not_ge he
    have hsub : (univ.filter (fun f => R f ≤ s)) ⊂ (univ.filter (fun f => R f ≤ R e)) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(by intro f hf; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2.trans hlt.le⟩),?_⟩
      intro hh
      have he' : e ∈ univ.filter (fun f => R f ≤ s) := hh ▸ mem_filter.mpr ⟨mem_univ _,le_rfl⟩
      exact he (mem_filter.mp he').2
    have hh := card_lt_card hsub
    omega
  · intro he
    exact card_le_card ((by intro f hf; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hf).2.trans he⟩))

def packingChain (R : Fin m → ℝ) (q : ℕ) : PartitionChain n where
  parts i := G.packingParts (G.rankedEdges R i) q
  partition _i := G.packingParts_vertexPartition _ q
  coarsens _i _j hij := G.packingParts_coarsens (G.rankedEdges_mono R hij)

lemma packingChain_local (R : Fin m → ℝ) (q : ℕ) (i : ℕ) :
    ∀A ∈ (G.packingChain R q).parts i, G.EdgeConnectedReal A q := G.packingParts_local _ q

lemma packingChain_crossing (R : Fin m → ℝ) (q i : ℕ) :
    (G.packingChain R q).crossing G i=G.crossing univ (G.partLabel (G.rankedEdges R i) q) := by
  classical
  ext e
  rw [PartitionChain.mem_crossing]
  simp only [MultiGraph.crossing,mem_filter,mem_univ,true_and]
  rw [Ne,Ne,G.partLabel_eq_iff]
  have he (v : Fin n) : (G.packingChain R q).block i v=G.partOf (G.rankedEdges R i) q v := by
    apply (G.packingChain R q).block_eq_of_mem
    · exact mem_filter.mpr ⟨mem_univ _,(G.partOf_spec _ q v).2⟩
    · exact (G.partOf_spec _ q v).1
  rw [he,he]

lemma treePackable_mono_edges {F F' : Finset (Fin m)} {q : ℕ}
    (h : F ⊆ F') (hp : G.TreePackable F q) : G.TreePackable F' q := by
  obtain ⟨T,hT,hd⟩ := hp
  exact ⟨T,fun i => ⟨(hT i).1.trans h,(hT i).2⟩,hd⟩

lemma treePackable_mono_count {F : Finset (Fin m)} {q r : ℕ}
    (h : q ≤ r) (hp : G.TreePackable F r) : G.TreePackable F q := by
  obtain ⟨T,hT,hd⟩ := hp
  exact ⟨fun i => T (Fin.castLE h i),fun i => hT _,fun i j hij => hd (fun he => hij (Fin.castLE_injective h he))⟩

lemma packingChain_root (R : Fin m → ℝ) {q : ℕ} (hn : 0 < n) (hp : G.TreePackable univ q) :
    (G.packingChain R q).parts m={univ} := by
  change G.packingParts (G.rankedEdges R m) q={univ}
  rw [G.rankedEdges_full]
  exact G.packingParts_eq_root hn hp

end
end StrongThinTree.MultiGraph

end

end OAI
