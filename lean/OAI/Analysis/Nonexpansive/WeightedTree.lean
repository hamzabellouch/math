import OAI.Analysis.Nonexpansive.OrderedTree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Positive edge weights and the actual path mass

Path mass is defined recursively from the parent maps and edge weights.
Its normalization and its mass on every descendant block are consequences
of the normalization at each parent.
-/

open scoped BigOperators

namespace ReflexiveFixedPoints

/-- Partition a finite sum by the fibers of a function. -/
theorem sum_fiber_partition {A B M : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [AddCommMonoid M] (f : A → B) (g : A → M) :
    (∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), g a) = ∑ a, g a := by
  classical
  exact Finset.sum_fiberwise Finset.univ f g

/-- Regroup a weighted finite sum by the fibers of a function. -/
theorem sum_fiber_mul {A B R : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] [NonUnitalNonAssocSemiring R]
    (f : A → B) (r : B → R) (g : A → R) :
    (∑ b, r b * (∑ a ∈ Finset.univ.filter (fun a => f a = b), g a)) =
      ∑ a, r (f a) * g a := by
  classical
  calc
    _ = ∑ b, ∑ a ∈ Finset.univ.filter (fun a => f a = b), r (f a) * g a := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := sum_fiber_partition f _

/-- Positive edge weights, normalized separately over each parent's children. -/
structure WeightedTree (T : OrderedTree) where
  weight : (k : ℕ) → T.Node (k + 1) → ℝ
  weight_pos : ∀ k c, 0 < weight k c
  weight_sum : ∀ k p,
    (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p), weight k c) = 1

namespace WeightedTree

variable {T : OrderedTree} (W : WeightedTree T)

theorem weight_nonneg (k : ℕ) (c : T.Node (k + 1)) : 0 ≤ W.weight k c :=
  (W.weight_pos k c).le

theorem weight_le_one (k : ℕ) (c : T.Node (k + 1)) : W.weight k c ≤ 1 := by
  calc
    W.weight k c ≤
        ∑ d ∈ Finset.univ.filter (fun d => T.parent k d = T.parent k c),
          W.weight k d :=
      Finset.single_le_sum (fun d _ => W.weight_nonneg k d) (by simp)
    _ = 1 := W.weight_sum k (T.parent k c)

/-- The product of the actual edge weights on the path from the root. -/
def pathWeight : (k : ℕ) → T.Node k → ℝ
  | 0, _ => 1
  | k + 1, c => pathWeight k (T.parent k c) * W.weight k c

@[simp] theorem pathWeight_zero (v : T.Node 0) : W.pathWeight 0 v = 1 := rfl

@[simp] theorem pathWeight_succ (k : ℕ) (c : T.Node (k + 1)) :
    W.pathWeight (k + 1) c = W.pathWeight k (T.parent k c) * W.weight k c := rfl

theorem pathWeight_pos (k : ℕ) (v : T.Node k) : 0 < W.pathWeight k v := by
  induction k with
  | zero => exact zero_lt_one
  | succ k ih => exact mul_pos (ih (T.parent k v)) (W.weight_pos k v)

theorem pathWeight_nonneg (k : ℕ) (v : T.Node k) : 0 ≤ W.pathWeight k v :=
  (W.pathWeight_pos k v).le

theorem pathWeight_le_one (k : ℕ) (v : T.Node k) : W.pathWeight k v ≤ 1 := by
  induction k with
  | zero => exact le_refl 1
  | succ k ih =>
      calc
        W.pathWeight (k + 1) v =
            W.pathWeight k (T.parent k v) * W.weight k v := rfl
        _ ≤ 1 * 1 :=
          mul_le_mul (ih (T.parent k v)) (W.weight_le_one k v)
            (W.weight_nonneg k v) zero_le_one
        _ = 1 := one_mul 1

/-- The parent map pushes the child path masses to the parent path masses. -/
theorem sum_pathWeight_parent (k : ℕ) (f : T.Node k → ℝ) :
    (∑ c, W.pathWeight (k + 1) c * f (T.parent k c)) =
      ∑ p, W.pathWeight k p * f p := by
  calc
    _ = ∑ c, (W.pathWeight k (T.parent k c) * f (T.parent k c)) * W.weight k c := by
      apply Finset.sum_congr rfl
      intro c _
      rw [W.pathWeight_succ]
      exact mul_right_comm (W.pathWeight k (T.parent k c)) (W.weight k c)
        (f (T.parent k c))
    _ = ∑ p, (W.pathWeight k p * f p) *
        (∑ c ∈ Finset.univ.filter (fun c => T.parent k c = p), W.weight k c) :=
      (sum_fiber_mul (T.parent k) (fun p => W.pathWeight k p * f p) (W.weight k)).symm
    _ = _ := by simp only [W.weight_sum, mul_one]

theorem sum_pathWeight (k : ℕ) : (∑ v, W.pathWeight k v) = 1 := by
  induction k with
  | zero => simp [pathWeight, OrderedTree.Node, T.size_zero]
  | succ k ih =>
      calc
        (∑ v, W.pathWeight (k + 1) v) = ∑ p, W.pathWeight k p := by
          simpa only [mul_one] using W.sum_pathWeight_parent k (fun _ => 1)
        _ = 1 := ih

/-- Every ancestor map pushes later-level path masses to earlier-level masses. -/
theorem sum_pathWeight_ancestor {i j : ℕ} (h : i ≤ j) (f : T.Node i → ℝ) :
    (∑ v, W.pathWeight j v * f (T.ancestorLE h v)) =
      ∑ p, W.pathWeight i p * f p := by
  induction h using Nat.leRec with
  | refl => simp
  | @le_succ_of_le j h ih =>
      calc
        _ = ∑ v, W.pathWeight (j + 1) v * f (T.ancestorLE h (T.parent j v)) := by
          simp only [T.ancestorLE_step_apply h]
        _ = ∑ p, W.pathWeight j p * f (T.ancestorLE h p) :=
          W.sum_pathWeight_parent j (fun p => f (T.ancestorLE h p))
        _ = _ := ih

/-- The total mass below a node is exactly that node's path mass. -/
theorem descendant_sum_pathWeight {i j : ℕ} (h : i ≤ j) (p : T.Node i) :
    (∑ v ∈ T.descendants h p, W.pathWeight j v) = W.pathWeight i p := by
  classical
  have hf := W.sum_pathWeight_ancestor h (fun q => if q = p then (1 : ℝ) else 0)
  simpa [OrderedTree.descendants, Finset.sum_filter, mul_ite] using hf

theorem pathWeight_le_ancestor {i j : ℕ} (h : i ≤ j) (v : T.Node j) :
    W.pathWeight j v ≤ W.pathWeight i (T.ancestorLE h v) := by
  calc
    W.pathWeight j v ≤
        ∑ s ∈ T.descendants h (T.ancestorLE h v), W.pathWeight j s :=
      Finset.single_le_sum (fun s _ => W.pathWeight_nonneg j s) (by simp)
    _ = _ := W.descendant_sum_pathWeight h (T.ancestorLE h v)

theorem pathWeight_ratio_pos {i j : ℕ} (h : i ≤ j) (v : T.Node j) :
    0 < W.pathWeight j v / W.pathWeight i (T.ancestorLE h v) :=
  div_pos (W.pathWeight_pos j v) (W.pathWeight_pos i (T.ancestorLE h v))

theorem pathWeight_ratio_le_one {i j : ℕ} (h : i ≤ j) (v : T.Node j) :
    W.pathWeight j v / W.pathWeight i (T.ancestorLE h v) ≤ 1 :=
  (div_le_one (W.pathWeight_pos i (T.ancestorLE h v))).2 (W.pathWeight_le_ancestor h v)

end WeightedTree
end ReflexiveFixedPoints

end OAI
