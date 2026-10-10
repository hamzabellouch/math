import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorRefinement

namespace OAI

/-! # Live buffers in every interrupted separator traversal

The execution below follows the same guarded calls and result branches as
`BudgetedSeparatorTraversal.execute`. Its additional field counts the
retained list/continuation cells. `scratch` accounts separately for the
interval-query callback's temporary cells. Entry payloads and incidence
tables remain shared. Sequential children retain only a Boolean result.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorCells

open BudgetedSeparatorCall BudgetedSeparatorFlow

abbrev Execution (α : Type*) := Outcome α × ℕ

variable {α β γ : Type*}

def seq (first : Execution α) (next : α → ℕ → Execution β) : Execution β :=
  match first.1.1 with
  | none => ((none, first.1.2), first.2)
  | some (a, left) =>
    let out := next a left
    ((out.1.1, first.1.2 + out.1.2), max first.2 out.2)

def scope (resident : ℕ) (first : Outcome α) (next : α → ℕ → Execution β) : Execution β :=
  match first.1 with
  | none => ((none, first.2), resident)
  | some (a, left) =>
    let out := next a left
    ((out.1.1, first.2 + out.1.2), resident + out.2)

theorem seq_value (first : Execution α) (next : α → ℕ → Execution β) :
    (seq first next).1 = bind first.1 (fun a left => (next a left).1) := by
  simp only [seq, BudgetedSeparatorFlow.bind]
  split <;> simp_all only

theorem scope_value (resident : ℕ) (first : Outcome α) (next : α → ℕ → Execution β) :
    (scope resident first next).1 = bind first (fun a left => (next a left).1) := by
  simp only [scope, BudgetedSeparatorFlow.bind]
  split <;> simp_all only

theorem seq_cells (first : Execution α) (next : α → ℕ → Execution β) (L : ℕ)
    (hfirst : first.2 ≤ L) (hnext : ∀ a left, (next a left).2 ≤ L) :
    (seq first next).2 ≤ L := by
  simp only [seq]
  split
  · exact hfirst
  · exact max_le hfirst (hnext _ _)

theorem scope_cells (resident : ℕ) (first : Outcome α) (next : α → ℕ → Execution β) (L : ℕ)
    (hnext : ∀ a left, first.1 = some (a, left) → (next a left).2 ≤ L) :
    (scope resident first next).2 ≤ resident + L := by
  simp only [scope]
  split
  · omega
  · rename_i a left h
    exact Nat.add_le_add_left (hnext a left h) resident

def run (scratch K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → Execution Bool) :
    ℕ → ℕ → ℕ → List α → List β → ℕ → ℕ → ℕ → Execution Bool
  | 0, lo, hi, xs, ys, nx, ny, budget =>
    scope (8 * (nx + ny + 1) + scratch)
      (BudgetedSeparatorNode.run K test₁ test₂ lo hi xs ys nx ny budget) fun f left =>
        if f.left.isEmpty || f.right.isEmpty then (BudgetedSeparatorFlow.pure false left, 0)
        else leaf lo f.left f.right f.nx f.ny left
  | k + 1, lo, hi, xs, ys, nx, ny, budget =>
    scope (8 * (nx + ny + 1) + scratch)
      (BudgetedSeparatorNode.run K test₁ test₂ lo hi xs ys nx ny budget) fun f left =>
        if f.left.isEmpty || f.right.isEmpty then (BudgetedSeparatorFlow.pure false left, 0)
        else if hi ≤ lo + 1 then leaf lo f.left f.right f.nx f.ny left
        else
          let mid := (lo + hi) / 2
          seq (run scratch K test₁ test₂ leaf k lo mid f.left f.right f.nx f.ny left)
            fun a remaining =>
              seq (run scratch K test₁ test₂ leaf k mid hi f.left f.right f.nx f.ny remaining)
                fun b rest => (BudgetedSeparatorFlow.pure (a || b) rest, 0)

theorem run_value (scratch K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → Execution Bool)
    (k lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ) :
    (run scratch K test₁ test₂ leaf k lo hi xs ys nx ny budget).1 =
      BudgetedSeparatorTraversal.execute K test₁ test₂
        (fun j as bs na nb rem => (leaf j as bs na nb rem).1) k lo hi xs ys nx ny budget := by
  induction k generalizing lo hi xs ys nx ny budget with
  | zero =>
    simp only [run, scope_value, BudgetedSeparatorTraversal.execute]
    congr 1
    funext f left
    split <;> rfl
  | succ k ih =>
    simp only [run, scope_value, BudgetedSeparatorTraversal.execute]
    congr 1
    funext f left
    split
    · rfl
    · split
      · rfl
      · simp only [seq_value, ih]

private theorem child_size (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ) (lo hi : ℕ) (xs : List α) (ys : List β) :
    (BudgetedSeparatorNode.prepare test₁ test₂ lo hi xs ys).1.left.length +
      (BudgetedSeparatorNode.prepare test₁ test₂ lo hi xs ys).1.right.length ≤
      xs.length + ys.length := by
  have hl := List.length_filter_le (fun x => (test₁ x lo hi).1) xs
  have hr := List.length_filter_le (fun y => (test₂ y lo hi).1) ys
  simpa only [BudgetedSeparatorNode.prepare, MeasuredSeparatorTraversal.keep,
    MeasuredFilter.runAcc_value, List.reverse_nil, List.nil_append] using Nat.add_le_add hl hr

theorem run_cells (scratch K C L : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → Execution Bool)
    (hleaf : ∀ j as bs na nb rem, as.length = na → bs.length = nb →
      as.length + bs.length ≤ C → (leaf j as bs na nb rem).2 ≤ L)
    (k lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) (hsize : nx + ny ≤ C) :
    (run scratch K test₁ test₂ leaf k lo hi xs ys nx ny budget).2 ≤
      (k + 1) * (8 * (C + 1) + scratch) + L := by
  induction k generalizing lo hi xs ys nx ny budget with
  | zero =>
    rw [run]
    refine le_trans (scope_cells (8 * (nx + ny + 1) + scratch)
      (BudgetedSeparatorNode.run K test₁ test₂ lo hi xs ys nx ny budget) _ L ?_) ?_
    · intro f left hf
      obtain ⟨rfl, _, _⟩ := BudgetedSeparatorNode.value K test₁ test₂ lo hi xs ys
        nx ny budget f left hf
      have hc := child_size test₁ test₂ lo hi xs ys
      rw [hx, hy] at hc
      split
      · exact Nat.zero_le L
      · exact hleaf _ _ _ _ _ _ rfl rfl (hc.trans hsize)
    · nlinarith only [hsize]
  | succ k ih =>
    rw [run]
    refine le_trans (scope_cells (8 * (nx + ny + 1) + scratch)
      (BudgetedSeparatorNode.run K test₁ test₂ lo hi xs ys nx ny budget) _
      ((k + 1) * (8 * (C + 1) + scratch) + L) ?_) ?_
    · intro f left hf
      obtain ⟨rfl, _, _⟩ := BudgetedSeparatorNode.value K test₁ test₂ lo hi xs ys
        nx ny budget f left hf
      have hc := child_size test₁ test₂ lo hi xs ys
      rw [hx, hy] at hc
      have hc' := hc.trans hsize
      split
      · exact Nat.zero_le _
      · split
        · exact (hleaf _ _ _ _ _ _ rfl rfl hc').trans (by omega)
        · apply seq_cells
          · exact ih _ _ _ _ _ _ _ rfl rfl hc'
          · intro a remaining
            apply seq_cells
            · exact ih _ _ _ _ _ _ _ rfl rfl hc'
            · intro b rest
              exact Nat.zero_le _
    · nlinarith only [hsize]

end LowSpaceSubsetSum.BudgetedSeparatorCells

end OAI
