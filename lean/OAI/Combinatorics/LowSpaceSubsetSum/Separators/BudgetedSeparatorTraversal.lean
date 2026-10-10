import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorNode
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorFlow

namespace OAI

/-! # Budgeted depth-first traversal of one separator block

Every node reserves its filter allowance before inspecting record masks.
The two recursive branches execute in order, passing the remaining budget;
only their Boolean results survive. List lengths are cached in each frame.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorTraversal

open BudgetedSeparatorCall BudgetedSeparatorFlow

variable {α β : Type*}

def execute (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → Outcome Bool) :
    ℕ → ℕ → ℕ → List α → List β → ℕ → ℕ → ℕ → Outcome Bool
  | 0, lo, hi, xs, ys, nx, ny, budget =>
    bind (BudgetedSeparatorNode.run K test₁ test₂ lo hi xs ys nx ny budget) fun f left =>
      if f.left.isEmpty || f.right.isEmpty then pure false left
      else leaf lo f.left f.right f.nx f.ny left
  | k + 1, lo, hi, xs, ys, nx, ny, budget =>
    bind (BudgetedSeparatorNode.run K test₁ test₂ lo hi xs ys nx ny budget) fun f left =>
      if f.left.isEmpty || f.right.isEmpty then pure false left
      else if hi ≤ lo + 1 then leaf lo f.left f.right f.nx f.ny left
      else
        let mid := (lo + hi) / 2
        bind (execute K test₁ test₂ leaf k lo mid f.left f.right f.nx f.ny left)
          fun first remaining =>
            bind (execute K test₁ test₂ leaf k mid hi f.left f.right f.nx f.ny remaining)
              fun second rest => pure (first || second) rest

theorem account (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (h₁ : ∀ x lo hi, (test₁ x lo hi).2 ≤ K)
    (h₂ : ∀ y lo hi, (test₂ y lo hi).2 ≤ K)
    (leaf : ℕ → List α → List β → ℕ → ℕ → ℕ → Outcome Bool)
    (hleaf : ∀ j as bs na nb budget, as.length = na → bs.length = nb →
      Account budget (leaf j as bs na nb budget))
    (k lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) :
    Account budget (execute K test₁ test₂ leaf k lo hi xs ys nx ny budget) := by
  induction k generalizing lo hi xs ys nx ny budget with
  | zero =>
    rw [execute]
    apply bind_account
    · exact ⟨BudgetedSeparatorNode.work K test₁ test₂ h₁ h₂ lo hi xs ys nx ny budget hx hy,
        fun f left hf => BudgetedSeparatorNode.spent K test₁ test₂ h₁ h₂
          lo hi xs ys nx ny budget hx hy f left hf⟩
    · intro f left _
      split
      · exact pure_account _ _
      · exact hleaf lo f.left f.right f.nx f.ny left f.left_size f.right_size
  | succ k ih =>
    rw [execute]
    apply bind_account
    · exact ⟨BudgetedSeparatorNode.work K test₁ test₂ h₁ h₂ lo hi xs ys nx ny budget hx hy,
        fun f left hf => BudgetedSeparatorNode.spent K test₁ test₂ h₁ h₂
          lo hi xs ys nx ny budget hx hy f left hf⟩
    · intro f left _
      split
      · exact pure_account _ _
      · split
        · exact hleaf lo f.left f.right f.nx f.ny left f.left_size f.right_size
        · apply bind_account
          · exact ih _ _ _ _ _ _ _ f.left_size f.right_size
          · intro first remaining _
            apply bind_account
            · exact ih _ _ _ _ _ _ _ f.left_size f.right_size
            · intro second rest _
              exact pure_account _ _

def reference (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ) (leaf : ℕ → List α → List β → Bool × ℕ) :
    ℕ → ℕ → ℕ → List α → List β → Bool × ℕ
  | 0, lo, hi, xs, ys =>
    let f := (BudgetedSeparatorNode.prepare test₁ test₂ lo hi xs ys).1
    let fee := BudgetedSeparatorNode.charge K xs.length ys.length
    if f.left.isEmpty || f.right.isEmpty then (false, fee)
    else
      let out := leaf lo f.left f.right
      (out.1, fee + out.2)
  | k + 1, lo, hi, xs, ys =>
    let f := (BudgetedSeparatorNode.prepare test₁ test₂ lo hi xs ys).1
    let fee := BudgetedSeparatorNode.charge K xs.length ys.length
    if f.left.isEmpty || f.right.isEmpty then (false, fee)
    else if hi ≤ lo + 1 then
      let out := leaf lo f.left f.right
      (out.1, fee + out.2)
    else
      let mid := (lo + hi) / 2
      let first := reference K test₁ test₂ leaf k lo mid f.left f.right
      let second := reference K test₁ test₂ leaf k mid hi f.left f.right
      (first.1 || second.1, fee + first.2 + second.2)

end LowSpaceSubsetSum.BudgetedSeparatorTraversal

end OAI
