import OAI.NumberTheory.TwoPoint.Bounds.FiniteWalkFamily
import OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder

namespace OAI

/-! A single bounded numbering of all vertices observed in a finite walk family. -/

namespace TwoPointCorrelations

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {segments N : ℕ}

/-- The forest code comes with a numbering of the actual observed vertices.
It is injective across the whole family, so line numbers encode equality
between runs in different segments as well as within each segment. -/
theorem finite_walk_family_numbering
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hG : G.IsAcyclic) (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges)
    (hsize : (∑ i, (p i).support.length) ≤ N) (color : V → Bool) :
    ∃ (number : V → ℕ) (code : ForestPathData.Code N segments),
      Set.InjOn number (walkFamilySupport start finish p : Set V) ∧
      (∀ v ∈ walkFamilySupport start finish p, number v < N) ∧
      ∀ i, decodeForestPaths code i = (p i).support.map number := by
  classical
  obtain ⟨t, ht, hcover, d, hd⟩ := finite_walk_family_realizable start finish p hG hp hsize color
  let index : (walkFamilySupport start finish p) → ℕ :=
    fun v => @List.idxOf _ instBEqOfDecidableEq v (forestNodes t)
  let number : V → ℕ := fun v =>
    if hv : v ∈ walkFamilySupport start finish p then index ⟨v, hv⟩ else 0
  have hnumber (v : walkFamilySupport start finish p) : number v.val = index v := by
    simp only [number, dite_eq_left v.property]
  have hindex : Function.Injective index := preorder_index_injective t hcover
  have hnodes : (forestNodes t).length ≤ N := by
    rw [forestNodes_length, forest_representation_numNodes t ht hcover, Fintype.card_coe]
    exact (walkFamilySupport_card_le start finish p).trans hsize
  refine ⟨number, d.code, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have heq : index ⟨a, ha⟩ = index ⟨b, hb⟩ := by
      simpa only [← hnumber] using hab
    exact congrArg Subtype.val (hindex heq)
  · intro v hv
    let : BEq (walkFamilySupport start finish p) := instBEqOfDecidableEq
    rw [show number v = index ⟨v, hv⟩ from hnumber ⟨v, hv⟩]
    exact (List.idxOf_lt_length_iff.mpr (hcover ⟨v, hv⟩)).trans_le hnodes
  · intro i
    rw [decodeForestPaths_code]
    have hi := congrFun hd i
    change d.pattern i = (restrictedFamilyWalk start finish p i).support.map index at hi
    rw [hi]
    have hm : (restrictedFamilyWalk start finish p i).map (Embedding.induce _).toHom = p i :=
      Walk.map_induce (p i) (mem_walkFamilySupport start finish p i)
    have hs : (p i).support = (restrictedFamilyWalk start finish p i).support.map
        (fun v => v.val) := by
      exact (congrArg (fun q : G.Walk (start i) (finish i) => q.support) hm).symm.trans
        (Walk.support_map _ _)
    rw [hs, List.map_map]
    apply List.map_congr_left
    intro v _
    exact (hnumber v).symm

end TwoPointCorrelations

end OAI
