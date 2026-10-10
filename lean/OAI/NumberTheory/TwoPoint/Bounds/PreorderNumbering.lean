import OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
import Mathlib.Data.List.Basic

namespace OAI

/-! Preorder numbering depends only on the ordered forest shape. -/

namespace TwoPointCorrelations

open BinaryTree

variable {V W : Type*}

lemma forest_map_congr (t : BinaryTree V) (f g : V → W)
    (h : ∀ x ∈ forestNodes t, f x = g x) : t.map f = t.map g := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      simp only [BinaryTree.map]
      congr 1
      · exact h v (by simp [forestNodes])
      · exact hl (fun x hx => h x (by simp [forestNodes, hx]))
      · exact hr (fun x hx => h x (by simp [forestNodes, hx]))


@[simp] lemma forest_numNodes_map (f : V → W) (t : BinaryTree V) :
    (t.map f).numNodes = t.numNodes := by
  induction t <;> simp [BinaryTree.map, *]

def numberForest : BinaryTree V → ℕ → BinaryTree ℕ
  | .nil, _ => .nil
  | .node _ l r, start =>
      .node start (numberForest l (start + 1)) (numberForest r (start + 1 + l.numNodes))

@[simp] lemma numberForest_map (f : V → W) (t : BinaryTree V) (start : ℕ) :
    numberForest (t.map f) start = numberForest t start := by
  induction t generalizing start <;> simp [BinaryTree.map, numberForest, *]

lemma numberForest_eq_map_idxOf [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (start : ℕ) :
    numberForest t start = t.map (fun v => start + (forestNodes t).idxOf v) := by
  induction t generalizing start with
  | nil => rfl
  | node v l r hl hr =>
      have hn := List.nodup_cons.mp ht
      have hp := List.nodup_append.mp hn.2
      simp only [numberForest, BinaryTree.map]
      congr 1
      · simp [forestNodes]
      · rw [hl hp.1 (start + 1)]
        apply forest_map_congr
        intro x hx
        have hv : v ≠ x := by intro heq; subst x; exact hn.1 (List.mem_append_left _ hx)
        simp only [forestNodes, List.idxOf_cons_ne _ hv, List.idxOf_append_of_mem hx]
        omega
      · rw [hr hp.2.1 (start + 1 + l.numNodes)]
        apply forest_map_congr
        intro x hx
        have hv : v ≠ x := by intro heq; subst x; exact hn.1 (List.mem_append_right _ hx)
        have hxl : x ∉ forestNodes l := by
          intro hxl
          exact hp.2.2 x hxl x hx rfl
        simp only [forestNodes, List.idxOf_cons_ne _ hv, List.idxOf_append_of_notMem hxl,
          forestNodes_length]
        omega

/-- Thus erasing numerical labels preserves the canonical numbered graph. -/
theorem numberForest_eq_of_same_shape (t : BinaryTree V) (s : BinaryTree W)
    (hts : t.map (fun _ => ()) = s.map (fun _ => ())) (start : ℕ) :
    numberForest t start = numberForest s start := by
  have h := congrArg (fun a => numberForest a start) hts
  simpa only [numberForest_map] using h

lemma preorder_index_injective [DecidableEq V] (t : BinaryTree V)
    (hcover : ∀ v, v ∈ forestNodes t) :
    Function.Injective (fun v => (forestNodes t).idxOf v) := by
  intro x y hxy
  exact (List.idxOf_inj (hcover x)).mp hxy

/-- Numbering transports every edge without retaining its original labels. -/
theorem numberForest_adjacent [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hcover : ∀ v, v ∈ forestNodes t) (x y : V) :
    forestAdjacent (numberForest t 0) ((forestNodes t).idxOf x) ((forestNodes t).idxOf y) ↔
      forestAdjacent t x y := by
  rw [numberForest_eq_map_idxOf t ht 0]
  simpa only [zero_add] using forestAdjacent_map
    (fun v => (forestNodes t).idxOf v) (preorder_index_injective t hcover) t x y

end TwoPointCorrelations

end OAI
