import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCall
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.MeasuredSeparatorTraversal

namespace OAI

/-! # Prepaid filter nodes with cached output lengths

The successful node retains only filtered lists and two scalar lengths.
Its whole filtering, length computation and branch bookkeeping is reserved
before either interval predicate is evaluated.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorNode

variable {α β : Type*}

structure Frame (α β : Type*) where
  left : List α
  right : List β
  nx : ℕ
  ny : ℕ
  left_size : left.length = nx
  right_size : right.length = ny

def prepare (test₁ : α → ℕ → ℕ → Bool × ℕ) (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (lo hi : ℕ) (xs : List α) (ys : List β) : Frame α β × ℕ :=
  let a := MeasuredSeparatorTraversal.keep test₁ lo hi xs
  let b := MeasuredSeparatorTraversal.keep test₂ lo hi ys
  let nx := a.1.length
  let ny := b.1.length
  (⟨a.1, b.1, nx, ny, rfl, rfl⟩, a.2 + b.2 + 2 * (nx + ny) + 12)

def charge (K nx ny : ℕ) : ℕ := (K + 20) * (nx + ny + 1)

theorem prepare_work (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ) (K : ℕ)
    (h₁ : ∀ x lo hi, (test₁ x lo hi).2 ≤ K)
    (h₂ : ∀ y lo hi, (test₂ y lo hi).2 ≤ K)
    (lo hi : ℕ) (xs : List α) (ys : List β) :
    (prepare test₁ test₂ lo hi xs ys).2 + 1 ≤ charge K xs.length ys.length := by
  have ha := MeasuredSeparatorTraversal.keep_work test₁ K h₁ lo hi xs
  have hb := MeasuredSeparatorTraversal.keep_work test₂ K h₂ lo hi ys
  have hla : (MeasuredSeparatorTraversal.keep test₁ lo hi xs).1.length ≤ xs.length := by
    simp only [MeasuredSeparatorTraversal.keep, MeasuredFilter.runAcc_value,
      List.reverse_nil, List.nil_append]
    exact List.length_filter_le _ _
  have hlb : (MeasuredSeparatorTraversal.keep test₂ lo hi ys).1.length ≤ ys.length := by
    simp only [MeasuredSeparatorTraversal.keep, MeasuredFilter.runAcc_value,
      List.reverse_nil, List.nil_append]
    exact List.length_filter_le _ _
  unfold prepare charge
  dsimp only
  nlinarith only [ha, hb, hla, hlb, Nat.zero_le K, Nat.zero_le xs.length, Nat.zero_le ys.length]

def run (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ) (lo hi : ℕ)
    (xs : List α) (ys : List β) (nx ny budget : ℕ) :
    BudgetedSeparatorCall.Outcome (Frame α β) :=
  BudgetedSeparatorCall.run (charge K nx ny)
    (fun _ => prepare test₁ test₂ lo hi xs ys) budget

theorem work (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (h₁ : ∀ x lo hi, (test₁ x lo hi).2 ≤ K)
    (h₂ : ∀ y lo hi, (test₂ y lo hi).2 ≤ K)
    (lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) :
    (run K test₁ test₂ lo hi xs ys nx ny budget).2 ≤ budget + 1 := by
  apply BudgetedSeparatorCall.work
  simpa only [hx, hy] using prepare_work test₁ test₂ K h₁ h₂ lo hi xs ys

theorem spent (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ)
    (h₁ : ∀ x lo hi, (test₁ x lo hi).2 ≤ K)
    (h₂ : ∀ y lo hi, (test₂ y lo hi).2 ≤ K)
    (lo hi : ℕ) (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny)
    (out : Frame α β) (left : ℕ)
    (h : (run K test₁ test₂ lo hi xs ys nx ny budget).1 = some (out, left)) :
    left ≤ budget ∧ (run K test₁ test₂ lo hi xs ys nx ny budget).2 ≤ budget - left := by
  apply BudgetedSeparatorCall.spent _ _ _ ?_ _ _ h
  simpa only [hx, hy] using prepare_work test₁ test₂ K h₁ h₂ lo hi xs ys

theorem value (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ) (lo hi : ℕ)
    (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (out : Frame α β) (left : ℕ)
    (h : (run K test₁ test₂ lo hi xs ys nx ny budget).1 = some (out, left)) :
    out = (prepare test₁ test₂ lo hi xs ys).1 ∧
      left = budget - charge K nx ny ∧ charge K nx ny ≤ budget :=
  BudgetedSeparatorCall.value _ _ _ _ _ h

theorem complete (K : ℕ) (test₁ : α → ℕ → ℕ → Bool × ℕ)
    (test₂ : β → ℕ → ℕ → Bool × ℕ) (lo hi : ℕ)
    (xs : List α) (ys : List β) (nx ny budget : ℕ)
    (h : charge K nx ny ≤ budget) :
    (run K test₁ test₂ lo hi xs ys nx ny budget).1 =
      some ((prepare test₁ test₂ lo hi xs ys).1, budget - charge K nx ny) := by
  rw [run, BudgetedSeparatorCall.complete _ _ _ h]

end LowSpaceSubsetSum.BudgetedSeparatorNode

end OAI
