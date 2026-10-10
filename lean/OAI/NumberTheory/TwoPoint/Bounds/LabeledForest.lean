import Mathlib.Data.Tree.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open BinaryTree

variable {V : Type*}

def forestNodes : BinaryTree V → List V
  | .nil => []
  | .node v children siblings => v :: (forestNodes children ++ forestNodes siblings)

def forestRoots : BinaryTree V → List V
  | .nil => []
  | .node v _ siblings => v :: forestRoots siblings

def forestAdjacent : BinaryTree V → V → V → Prop
  | .nil, _, _ => False
  | .node v children siblings, x, y =>
      (x = v ∧ y ∈ forestRoots children) ∨ (y = v ∧ x ∈ forestRoots children) ∨
        forestAdjacent children x y ∨ forestAdjacent siblings x y

@[simp] lemma forestNodes_length (t : BinaryTree V) : (forestNodes t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node v l r hl hr => simp [forestNodes, hl, hr]

lemma forestRoots_subset (t : BinaryTree V) : forestRoots t ⊆ forestNodes t := by
  induction t with
  | nil => simp [forestRoots, forestNodes]
  | node v l r hl hr =>
      intro x hx
      simp only [forestRoots, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [forestNodes]
      · simp [forestNodes, hr hx]

lemma forestAdjacent_symm (t : BinaryTree V) (x y : V) :
    forestAdjacent t x y ↔ forestAdjacent t y x := by
  induction t with
  | nil => rfl
  | node v l r hl hr => simp only [forestAdjacent, hl, hr]; tauto

lemma forestAdjacent_mem (t : BinaryTree V) {x y : V} (h : forestAdjacent t x y) :
    x ∈ forestNodes t ∧ y ∈ forestNodes t := by
  induction t with
  | nil => exact h.elim
  | node v l r hl hr =>
      rcases h with ⟨rfl, hy⟩ | ⟨rfl, hx⟩ | h | h
      · simp [forestNodes, forestRoots_subset l hy]
      · simp [forestNodes, forestRoots_subset l hx]
      · obtain ⟨hx, hy⟩ := hl h
        simp [forestNodes, hx, hy]
      · obtain ⟨hx, hy⟩ := hr h
        simp [forestNodes, hx, hy]

lemma forestAdjacent_irrefl (t : BinaryTree V) (ht : (forestNodes t).Nodup) (x : V) :
    ¬forestAdjacent t x x := by
  induction t with
  | nil => exact id
  | node v l r hl hr =>
      have hnodup := List.nodup_cons.mp ht
      have hparts := List.nodup_append.mp hnodup.2
      intro h
      rcases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | h | h
      · exact hnodup.1 (List.mem_append_left _ (forestRoots_subset l hx))
      · exact hnodup.1 (List.mem_append_left _ (forestRoots_subset l hx))
      · exact hl hparts.1 h
      · exact hr hparts.2.1 h

/-- Add a fresh leaf as the first child of its unique parent. -/
def attachForestLeaf [DecidableEq V] (parent leaf : V) : BinaryTree V → BinaryTree V
  | .nil => .nil
  | .node v children siblings =>
      if v = parent then .node v (.node leaf .nil children) siblings
      else .node v (attachForestLeaf parent leaf children) (attachForestLeaf parent leaf siblings)

lemma attachForestLeaf_of_not_mem [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (hp : parent ∉ forestNodes t) : attachForestLeaf parent leaf t = t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      have hv : v ≠ parent := by intro h; subst v; exact hp (by simp [forestNodes])
      have hpl : parent ∉ forestNodes l := by intro h; exact hp (by simp [forestNodes, h])
      have hpr : parent ∉ forestNodes r := by intro h; exact hp (by simp [forestNodes, h])
      simp only [attachForestLeaf, ite_eq_right hv, hl hpl, hr hpr]

@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]

lemma attachForestLeaf_nodes_perm [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hp : parent ∈ forestNodes t) :
    (forestNodes (attachForestLeaf parent leaf t)).Perm (leaf :: forestNodes t) := by
  induction t with
  | nil => simp [forestNodes] at hp
  | node v l r hl hr =>
      have hnodup := List.nodup_cons.mp ht
      have hparts := List.nodup_append.mp hnodup.2
      by_cases hv : v = parent
      · simp only [attachForestLeaf, ite_eq_left hv, forestNodes, List.nil_append]
        exact List.Perm.swap _ _ _
      · have hp' : parent ∈ forestNodes l ∨ parent ∈ forestNodes r := by
          simpa only [forestNodes, List.mem_cons, List.mem_append, Ne.symm hv, false_or] using hp
        rcases hp' with hp' | hp'
        · have hpr : parent ∉ forestNodes r := by
            intro hpr
            exact hparts.2.2 parent hp' parent hpr rfl
          rw [attachForestLeaf, ite_eq_right hv, attachForestLeaf_of_not_mem parent leaf r hpr]
          simp only [forestNodes]
          exact ((hl hparts.1 hp').append_right _).cons v |>.trans (List.Perm.swap _ _ _)
        · have hpl : parent ∉ forestNodes l := by
            intro hpl
            exact hparts.2.2 parent hpl parent hp' rfl
          rw [attachForestLeaf, ite_eq_right hv, attachForestLeaf_of_not_mem parent leaf l hpl]
          simp only [forestNodes]
          have hperm := ((hr hparts.2.1 hp').append_left (forestNodes l)).cons v
          exact hperm.trans ((List.perm_middle.cons v).trans (List.Perm.swap _ _ _))



private lemma move_two_disjuncts (A B C D E F : Prop) :
    (A ∨ B ∨ (C ∨ E ∨ F) ∨ D) ↔ (A ∨ B ∨ C ∨ D) ∨ E ∨ F := by
  tauto

lemma attachForestLeaf_adjacent [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hp : parent ∈ forestNodes t) (x y : V) :
    forestAdjacent (attachForestLeaf parent leaf t) x y ↔
      forestAdjacent t x y ∨ (x = parent ∧ y = leaf) ∨ (y = parent ∧ x = leaf) := by
  induction t with
  | nil => simp [forestNodes] at hp
  | node v l r hl hr =>
      have hnodup := List.nodup_cons.mp ht
      have hparts := List.nodup_append.mp hnodup.2
      by_cases hv : v = parent
      · subst v
        rw [attachForestLeaf, ite_eq_left rfl]
        simp only [forestAdjacent, forestRoots, List.mem_cons,
          List.not_mem_nil, and_false, false_or, and_or_left]
        constructor
        · rintro ((h | h) | (h | h) | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inr h)
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
        · rintro ((h | h | h | h) | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inr (Or.inl (Or.inr h))
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl (Or.inl h))
      · have hp' : parent ∈ forestNodes l ∨ parent ∈ forestNodes r := by
          simpa only [forestNodes, List.mem_cons, List.mem_append, Ne.symm hv, false_or] using hp
        rcases hp' with hp' | hp'
        · have hpr : parent ∉ forestNodes r := by
            intro hpr
            exact hparts.2.2 parent hp' parent hpr rfl
          rw [attachForestLeaf, ite_eq_right hv, attachForestLeaf_of_not_mem parent leaf r hpr]
          simp only [forestAdjacent, attachForestLeaf_roots, hl hparts.1 hp']
          exact move_two_disjuncts _ _ _ _ _ _
        · have hpl : parent ∉ forestNodes l := by
            intro hpl
            exact hparts.2.2 parent hpl parent hp' rfl
          rw [attachForestLeaf, ite_eq_right hv, attachForestLeaf_of_not_mem parent leaf l hpl]
          simp only [forestAdjacent, hr hparts.2.1 hp', or_assoc]

lemma attachForestLeaf_nodup [DecidableEq V] (parent leaf : V) (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hp : parent ∈ forestNodes t) (hf : leaf ∉ forestNodes t) :
    (forestNodes (attachForestLeaf parent leaf t)).Nodup := by
  exact (attachForestLeaf_nodes_perm parent leaf t ht hp).nodup_iff.mpr
    (List.nodup_cons.mpr ⟨hf, ht⟩)

@[simp] lemma forestNodes_map {W : Type*} (f : V → W) (t : BinaryTree V) :
    forestNodes (t.map f) = (forestNodes t).map f := by
  induction t <;> simp [BinaryTree.map, forestNodes, *]

@[simp] lemma forestRoots_map {W : Type*} (f : V → W) (t : BinaryTree V) :
    forestRoots (t.map f) = (forestRoots t).map f := by
  induction t <;> simp [BinaryTree.map, forestRoots, *]

lemma forestAdjacent_map {W : Type*} (f : V → W) (hf : Function.Injective f)
    (t : BinaryTree V) (x y : V) :
    forestAdjacent (t.map f) (f x) (f y) ↔ forestAdjacent t x y := by
  induction t <;> simp [BinaryTree.map, forestAdjacent, hf.eq_iff, *]

end TwoPointCorrelations

end OAI
