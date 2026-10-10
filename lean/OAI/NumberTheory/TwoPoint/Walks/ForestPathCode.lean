import OAI.NumberTheory.TwoPoint.Walks.CanonicalForest

namespace OAI

/-! An endpoint pair in a numbered forest recovers an entire non-reversing walk. -/

namespace TwoPointCorrelations

open SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The support of a path is transported exactly by a graph isomorphism. -/
theorem forest_path_support_identified (e : G ≃g H) (hH : H.IsAcyclic)
    {a b : V} (p : G.Walk a b) (q : H.Walk (e a) (e b))
    (hp : p.IsPath) (hq : q.IsPath) : p.support.map e = q.support := by
  have heq : p.map e.toHom = q := by
    exact Subtype.mk.inj (hH.subsingleton_path (e a) (e b) |>.elim
      ⟨p.map e.toHom, hp.map e.injective⟩ ⟨q, hq⟩)
  have hh := congrArg SimpleGraph.Walk.support heq
  rw [SimpleGraph.Walk.support_map] at hh
  exact hh

/-- Equal shape and equal endpoint indices determine the same numbered walk,
independently of the numerical realization of the graph. -/
theorem represented_walk_same_code [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hG : ∀ a b, forestAdjacent t a b ↔ G.Adj a b)
    (hH : ∀ a b, forestAdjacent s a b ↔ H.Adj a b)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ()))
    (hGa : G.IsAcyclic) (hHa : H.IsAcyclic)
    {a b : V} (p : G.Walk a b)
    (q : H.Walk (forestShapeEquiv t s ht hc hs hd hshape a)
      (forestShapeEquiv t s ht hc hs hd hshape b))
    (hp : List.IsChain (· ≠ ·) p.edges) (hq : List.IsChain (· ≠ ·) q.edges) :
    p.support.map (fun v => (forestNodes t).idxOf v) =
      q.support.map (fun w => (forestNodes s).idxOf w) := by
  let e := representedGraphIso G H t s ht hc hs hd hG hH hshape
  have hsupport := forest_path_support_identified e hHa p q
    ((hGa.isPath_iff_isChain p).mpr hp) ((hHa.isPath_iff_isChain q).mpr hq)
  calc
    _ = (p.support.map e).map (fun w => (forestNodes s).idxOf w) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      exact (forestShapeEquiv_index t s ht hc hs hd hshape v).symm
    _ = _ := congrArg (List.map (fun w => (forestNodes s).idxOf w)) hsupport

/-- Endpoint indices suffice; the graphs may have different vertex types. -/
theorem represented_walk_same_endpoints [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hG : ∀ a b, forestAdjacent t a b ↔ G.Adj a b)
    (hH : ∀ a b, forestAdjacent s a b ↔ H.Adj a b)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ()))
    (hGa : G.IsAcyclic) (hHa : H.IsAcyclic)
    {a b : V} {c d : W} (p : G.Walk a b) (q : H.Walk c d)
    (hp : List.IsChain (· ≠ ·) p.edges) (hq : List.IsChain (· ≠ ·) q.edges)
    (ha : (forestNodes t).idxOf a = (forestNodes s).idxOf c)
    (hb : (forestNodes t).idxOf b = (forestNodes s).idxOf d) :
    p.support.map (fun v => (forestNodes t).idxOf v) =
      q.support.map (fun w => (forestNodes s).idxOf w) := by
  have hleft : forestShapeEquiv t s ht hc hs hd hshape a = c :=
    preorder_index_injective s hd ((forestShapeEquiv_index t s ht hc hs hd hshape a).trans ha)
  have hright : forestShapeEquiv t s ht hc hs hd hshape b = d :=
    preorder_index_injective s hd ((forestShapeEquiv_index t s ht hc hs hd hshape b).trans hb)
  have h := represented_walk_same_code t s ht hc hs hd hG hH hshape hGa hHa p
    (q.copy hleft.symm hright.symm) hp (by simpa only [Walk.edges_copy] using hq)
  simpa only [Walk.support_copy] using h

end TwoPointCorrelations

end OAI
