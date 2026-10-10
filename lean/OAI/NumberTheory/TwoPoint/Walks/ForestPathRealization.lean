import OAI.NumberTheory.TwoPoint.Walks.ForestPathCounting
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-! Arbitrary finite incidence forests fit the coefficient-independent path code. -/

namespace TwoPointCorrelations

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {N segments : ℕ}

omit [Fintype V] in
lemma list_idxOf_map_injective {W : Type*} [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (l : List V) (v : V) :
    (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases hav : a = v
      · simp [hav]
      · have hfv : f a ≠ f v := fun h => hav (hf h)
        simp only [List.map_cons, List.idxOf_cons_ne _ hfv, List.idxOf_cons_ne _ hav, ih]

/-- Relabeling by `Fin` changes no forest index. The graph, walks, and
non-reversal proofs are transported rather than postulated. -/
noncomputable def forestPathDataOfRepresentation
    (G : SimpleGraph V) (hG : G.IsAcyclic) (hN : Fintype.card V ≤ N)
    (t : BinaryTree V) (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (ha : ∀ a b, forestAdjacent t a b ↔ G.Adj a b) (color : V → Bool)
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) : ForestPathData N segments := by
  let e := Fintype.equivFin V
  let H := G.comap e.symm
  have hH : H.IsAcyclic := hG.of_comap e.symm.toEmbedding
  let f : G →g H := ⟨e, by
    intro a b hab
    change G.Adj (e.symm (e a)) (e.symm (e b))
    simpa only [Equiv.symm_apply_apply] using hab⟩
  refine {
    vertices := Fintype.card V
    vertex_bound := hN
    graph := H
    acyclic := hH
    tree := t.map e
    nodup := by rw [forestNodes_map]; exact ht.map e.injective
    cover := ?_
    adjacent := ?_
    color := color ∘ e.symm
    start := e ∘ start
    finish := e ∘ finish
    walk := fun i => (p i).map f
    reduced := ?_ }
  · intro v
    rw [forestNodes_map]
    exact List.mem_map.mpr ⟨e.symm v, hc _, e.apply_symm_apply v⟩
  · intro a b
    have h := forestAdjacent_map e e.injective t (e.symm a) (e.symm b)
    change _ ↔ G.Adj (e.symm a) (e.symm b)
    simpa only [Equiv.apply_symm_apply] using h.trans (ha _ _)
  · intro i
    apply (hH.isPath_iff_isChain _).mp
    exact ((hG.isPath_iff_isChain _).mpr (hp i)).map e.injective

theorem forestPathDataOfRepresentation_pattern
    (G : SimpleGraph V) (hG : G.IsAcyclic) (hN : Fintype.card V ≤ N)
    (t : BinaryTree V) (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (ha : ∀ a b, forestAdjacent t a b ↔ G.Adj a b) (color : V → Bool)
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) :
    (forestPathDataOfRepresentation G hG hN t ht hc ha color start finish p hp).pattern =
      fun i => (p i).support.map (fun v => (forestNodes t).idxOf v) := by
  funext i
  simp only [ForestPathData.pattern, forestPathDataOfRepresentation, Walk.support_map,
    forestNodes_map, List.map_map]
  apply List.map_congr_left
  intro v _
  exact list_idxOf_map_injective (Fintype.equivFin V) (Fintype.equivFin V).injective _ v

/-- Every finite forest with boundedly many vertices and any family of
reduced walks contributes to the single universal code universe. -/
theorem forest_paths_realizable (G : SimpleGraph V) (hG : G.IsAcyclic)
    (hN : Fintype.card V ≤ N) (color : V → Bool)
    (start finish : Fin segments → V) (p : ∀ i, G.Walk (start i) (finish i))
    (hp : ∀ i, List.IsChain (· ≠ ·) (p i).edges) :
    ∃ t : BinaryTree V, (forestNodes t).Nodup ∧ (∀ v, v ∈ forestNodes t) ∧
      (fun i => (p i).support.map (fun v => (forestNodes t).idxOf v)) ∈
        Set.range (@ForestPathData.pattern N segments) := by
  obtain ⟨t, ht, hc, ha⟩ := exists_forest_representation G hG
  refine ⟨t, ht, hc, ?_⟩
  exact ⟨forestPathDataOfRepresentation G hG hN t ht hc ha color start finish p hp,
    forestPathDataOfRepresentation_pattern G hG hN t ht hc ha color start finish p hp⟩

end TwoPointCorrelations

end OAI
