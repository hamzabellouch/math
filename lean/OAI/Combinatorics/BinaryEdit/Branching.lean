import Mathlib

namespace OAI

/-!
# Counting active leaves in a full ordered tree

A node is its path, a list of child labels. `activeLeafCount A v h`
counts the active descendants exactly `h` edges below `v`. The condition
`BranchesAtLeast A k v h` concerns only internal nodes of that finite
subtree; it makes no assertion about children below its leaves.
-/

namespace TreeEdit.BinaryLower.Branching

variable {α : Type*} [Fintype α]

noncomputable def activeChildCount (A : List α → Prop) (v : List α) : ℕ :=
  by
    classical
    exact (Finset.univ.filter fun i => A (v ++ [i])).card

noncomputable def activeLeafCount (A : List α → Prop) (v : List α) : ℕ → ℕ
  | 0 => by
    classical
    exact if A v then 1 else 0
  | h + 1 => ∑ i : α, activeLeafCount A (v ++ [i]) h

def BranchesAtLeast (A : List α → Prop) (k : ℕ) (v : List α) : ℕ → Prop
  | 0 => True
  | h + 1 => (A v → k ≤ activeChildCount A v) ∧
      ∀ i : α, BranchesAtLeast A k (v ++ [i]) h

/-- If every active internal node has at least `k` active children,
then an active root has at least `k ^ h` active leaves at depth `h`.
No branching condition is imposed below depth `h`. -/
theorem pow_le_activeLeafCount (A : List α → Prop) (k h : ℕ)
    (v : List α) (hbranch : BranchesAtLeast A k v h) (hv : A v) :
    k ^ h ≤ activeLeafCount A v h := by
  classical
  induction h generalizing v with
  | zero => simp [activeLeafCount, hv]
  | succ h ih =>
    rcases hbranch with ⟨hroot, hchildren⟩
    let S : Finset α := Finset.univ.filter fun i => A (v ++ [i])
    have hcard : k ≤ S.card := hroot hv
    have hchild : ∀ i ∈ S, k ^ h ≤ activeLeafCount A (v ++ [i]) h := by
      intro i hi
      exact ih (v ++ [i]) (hchildren i) (Finset.mem_filter.mp hi).2
    calc
      k ^ (h + 1) = k ^ h * k := pow_succ k h
      _ ≤ k ^ h * S.card := Nat.mul_le_mul_left _ hcard
      _ = ∑ _i ∈ S, k ^ h := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ S, activeLeafCount A (v ++ [i]) h :=
        Finset.sum_le_sum hchild
      _ ≤ ∑ i : α, activeLeafCount A (v ++ [i]) h :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ S)
      _ = activeLeafCount A v (h + 1) := rfl

/-- A level-bounded local branching assumption supplies exactly the finite
recursive condition, with no assertion below the terminal level. -/
theorem branchesAtLeast_of_local (A : List α → Prop) (k H h : ℕ)
    (hlocal : ∀ v : List α, v.length < H → A v → k ≤ activeChildCount A v)
    (v : List α) (hv : v.length + h ≤ H) : BranchesAtLeast A k v h := by
  induction h generalizing v with
  | zero => trivial
  | succ h ih =>
    constructor
    · exact hlocal v (by omega)
    · intro i
      apply ih (v ++ [i])
      simp only [List.length_append, List.length_singleton]
      omega

/-- The recursive count is the ordinary finite cardinality of active
paths of length `h`, represented by functions on `Fin h`. -/
theorem activeLeafCount_eq_card (A : List α → Prop) [DecidablePred A] (v : List α) (h : ℕ) :
    activeLeafCount A v h =
      (Finset.univ.filter fun f : Fin h → α => A (v ++ List.ofFn f)).card := by
  classical
  induction h generalizing v with
  | zero =>
    by_cases hv : A v <;> simp [activeLeafCount, hv]
  | succ h ih =>
    rw [activeLeafCount, Finset.card_filter]
    calc
      (∑ i : α, activeLeafCount A (v ++ [i]) h) =
          ∑ i : α, ∑ f : Fin h → α,
            if A ((v ++ [i]) ++ List.ofFn f) then 1 else 0 := by
              simp only [ih, Finset.card_filter]
      _ = ∑ z : α × (Fin h → α),
            if A ((v ++ [z.1]) ++ List.ofFn z.2) then 1 else 0 :=
        (Fintype.sum_prod_type (fun z : α × (Fin h → α) =>
          if A ((v ++ [z.1]) ++ List.ofFn z.2) then (1 : ℕ) else 0)).symm
      _ = ∑ f : Fin (h + 1) → α,
            if A (v ++ List.ofFn f) then 1 else 0 := by
        apply Fintype.sum_equiv (Fin.consEquiv fun _ => α)
        intro z
        change (if A ((v ++ [z.1]) ++ List.ofFn z.2) then 1 else 0) =
          (if A (v ++ List.ofFn (Fin.cons z.1 z.2)) then 1 else 0)
        rw [List.ofFn_cons]
        simp only [List.append_assoc, List.singleton_append]

/-- Explicit cardinality form of the active branching bound. -/
theorem pow_le_card_active_paths (A : List α → Prop) [DecidablePred A] (k h : ℕ)
    (v : List α) (hbranch : BranchesAtLeast A k v h) (hv : A v) :
    k ^ h ≤
      (Finset.univ.filter fun f : Fin h → α => A (v ++ List.ofFn f)).card := by
  classical
  rw [← activeLeafCount_eq_card]
  exact pow_le_activeLeafCount A k h v hbranch hv

end TreeEdit.BinaryLower.Branching

end OAI
