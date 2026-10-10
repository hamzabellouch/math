import OAI.NumberTheory.TwoPoint.Walks.ForestPathRealization

namespace OAI

/-! Restricting a finite walk family to its observed vertices preserves its code. -/

namespace TwoPointCorrelations

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {segments N : ℕ}
  (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))

def walkFamilySupport : Finset V :=
  univ.biUnion (fun i => (p i).support.toFinset)

lemma mem_walkFamilySupport (i : Fin segments) (v : V) (hv : v ∈ (p i).support) :
    v ∈ walkFamilySupport start finish p :=
  mem_biUnion.mpr ⟨i, mem_univ _, List.mem_toFinset.mpr hv⟩

theorem walkFamilySupport_card_le :
    (walkFamilySupport start finish p).card ≤ ∑ i, (p i).support.length := by
  apply (card_biUnion_le).trans
  exact sum_le_sum (fun i _ => List.toFinset_card_le (p i).support)

abbrev walkFamilyGraph := G.induce (walkFamilySupport start finish p : Set V)

def walkFamilyStart (i : Fin segments) : (walkFamilySupport start finish p) :=
  ⟨start i, mem_walkFamilySupport start finish p i _ (p i).start_mem_support⟩

def walkFamilyFinish (i : Fin segments) : (walkFamilySupport start finish p) :=
  ⟨finish i, mem_walkFamilySupport start finish p i _ (p i).end_mem_support⟩

def restrictedFamilyWalk (i : Fin segments) :
    (walkFamilyGraph start finish p).Walk
      (walkFamilyStart start finish p i) (walkFamilyFinish start finish p i) :=
  (p i).induce _ (mem_walkFamilySupport start finish p i)

theorem restrictedFamilyWalk_reduced (hG : G.IsAcyclic)
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) (i : Fin segments) :
    List.IsChain (· ≠ ·) (restrictedFamilyWalk start finish p i).edges := by
  have hH := hG.induce (walkFamilySupport start finish p : Set V)
  apply (hH.isPath_iff_isChain _).mp
  apply (Walk.isPath_map_iff_of_injective (f := (Embedding.induce _).toHom)
    (show Function.Injective (Subtype.val : (walkFamilySupport start finish p) → V)
      from Subtype.val_injective)).mp
  have hm : (restrictedFamilyWalk start finish p i).map (Embedding.induce _).toHom = p i :=
    Walk.map_induce (p i) (mem_walkFamilySupport start finish p i)
  rw [hm]
  exact (hG.isPath_iff_isChain _).mpr (hp i)

/-- No finiteness hypothesis on the ambient graph is needed: the observed
support alone suffices for the universal forest code. -/
theorem finite_walk_family_realizable (hG : G.IsAcyclic)
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges)
    (hsize : (∑ i, (p i).support.length) ≤ N) (color : V → Bool) :
    ∃ t : BinaryTree (walkFamilySupport start finish p),
      (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
      (fun i => (restrictedFamilyWalk start finish p i).support.map
        (fun v => @List.idxOf _ instBEqOfDecidableEq v (forestNodes t))) ∈
          Set.range (@ForestPathData.pattern N segments) := by
  have hcard : Fintype.card (walkFamilySupport start finish p) ≤ N := by
    rw [Fintype.card_coe]
    exact (walkFamilySupport_card_le start finish p).trans hsize
  exact forest_paths_realizable (walkFamilyGraph start finish p) (hG.induce _) hcard
    (fun v => color v) (walkFamilyStart start finish p) (walkFamilyFinish start finish p)
    (restrictedFamilyWalk start finish p) (restrictedFamilyWalk_reduced start finish p hG hp)

end TwoPointCorrelations

end OAI
