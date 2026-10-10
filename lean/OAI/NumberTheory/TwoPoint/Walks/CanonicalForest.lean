import OAI.NumberTheory.TwoPoint.Walks.ForestRepresentation
import OAI.NumberTheory.TwoPoint.Bounds.PreorderNumbering
import Mathlib.Data.List.NodupEquivFin

namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open SimpleGraph BinaryTree

variable {V W : Type*}

/-- The finite index of a vertex is its first occurrence in preorder. -/
def forestIndexEquiv [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) :
    V ≃ Fin (forestNodes t).length :=
  (List.Nodup.getEquivOfForallMemList (forestNodes t) ht hc).symm

@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl

lemma forest_shape_length (t : BinaryTree V) (s : BinaryTree W)
    (h : t.map (fun _ => ()) = s.map (fun _ => ())) :
    (forestNodes t).length = (forestNodes s).length := by
  simpa only [forestNodes_length, forest_numNodes_map] using congrArg numNodes h

/-- This identification uses only the shape and the two preorder enumerations. -/
def forestShapeEquiv [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) : V ≃ W :=
  (forestIndexEquiv t ht hc).trans
    ((finCongr (forest_shape_length t s hshape)).trans (forestIndexEquiv s hs hd).symm)

@[simp] theorem forestShapeEquiv_index [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) (v : V) :
    (forestNodes s).idxOf (forestShapeEquiv t s ht hc hs hd hshape v) =
      (forestNodes t).idxOf v := by
  change (forestIndexEquiv s hs hd (forestShapeEquiv t s ht hc hs hd hshape v)).val = _
  simp only [forestShapeEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

/-- In particular the identification preserves parent/child incidence. -/
theorem forestShapeEquiv_adjacent [DecidableEq V] [DecidableEq W]
    (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) (a b : V) :
    forestAdjacent s (forestShapeEquiv t s ht hc hs hd hshape a)
      (forestShapeEquiv t s ht hc hs hd hshape b) ↔ forestAdjacent t a b := by
  rw [← numberForest_adjacent s hs hd, forestShapeEquiv_index, forestShapeEquiv_index,
    ← numberForest_eq_of_same_shape t s hshape 0, numberForest_adjacent t ht hc]

/-- A common erased shape gives an isomorphism of the represented graphs. -/
def representedGraphIso [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (t : BinaryTree V) (s : BinaryTree W)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t)
    (hs : (forestNodes s).Nodup) (hd : ∀ w, w ∈ forestNodes s)
    (hG : ∀ a b, forestAdjacent t a b ↔ G.Adj a b)
    (hH : ∀ a b, forestAdjacent s a b ↔ H.Adj a b)
    (hshape : t.map (fun _ => ()) = s.map (fun _ => ())) : G ≃g H where
  toEquiv := forestShapeEquiv t s ht hc hs hd hshape
  map_rel_iff' := by
    intro a b
    rw [← hH, forestShapeEquiv_adjacent t s ht hc hs hd hshape, hG]

end TwoPointCorrelations

end OAI
