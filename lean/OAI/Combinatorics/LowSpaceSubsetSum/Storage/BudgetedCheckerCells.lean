import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredTerminalCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredQueryCells
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorArrays

namespace OAI

/-! # Full interrupted-checker buffer lifetime

The header, the interval traversal and the terminal run in the same order
as the budgeted checker. The added peak field accounts for live temporary
lists and continuation cells; shared entry payloads and tables are external.
-/

namespace LowSpaceSubsetSum.BudgetedCheckerCells

open BudgetedSeparatorCells StoredSeparatorCheck

variable {n g : ℕ}

def run (scratch capacity : ℕ) (target : ℤ) :
    List (Block n g) → List (StoredEntry n) → List (StoredEntry n) →
      ℕ → ℕ → ℕ → Execution Bool
  | [], xs, ys, nx, ny, budget =>
    scope 8 (BudgetedSeparatorCheck.header capacity nx ny budget) fun fits left =>
      if fits then StoredTerminalCells.budgeted target xs ys nx ny left
      else (BudgetedSeparatorFlow.pure false left, 0)
  | b :: rest, xs, ys, nx, ny, budget =>
    scope 8 (BudgetedSeparatorCheck.header capacity nx ny budget) fun fits left =>
      if fits then
        BudgetedSeparatorCells.run scratch b.queryBound b.leftQuery b.rightQuery
          (fun _ as bs na nb remaining => run scratch capacity target rest as bs na nb remaining)
          b.depth 0 b.familySize xs ys nx ny left
      else (BudgetedSeparatorFlow.pure false left, 0)

theorem run_value (scratch capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (xs ys : List (StoredEntry n)) (nx ny budget : ℕ) :
    (run scratch capacity target blocks xs ys nx ny budget).1 =
      BudgetedSeparatorCheck.execute capacity target blocks xs ys nx ny budget := by
  induction blocks generalizing xs ys nx ny budget with
  | nil =>
    simp only [run, scope_value, BudgetedSeparatorCheck.execute]
    congr 1
    funext fits left
    split
    · exact StoredTerminalCells.budgeted_value _ _ _ _ _ _
    · rfl
  | cons b rest ih =>
    simp only [run, scope_value, BudgetedSeparatorCheck.execute]
    congr 1
    funext fits left
    split
    · simp only [BudgetedSeparatorCells.run_value, ih]
    · rfl

def bound (scratch n C : ℕ) : List (Block n g) → ℕ
  | [] => 8 + 72 * (n + 1) * (C + 1)
  | b :: rest => 8 + (b.depth + 1) * (8 * (C + 1) + scratch) + bound scratch n C rest

theorem run_cells (scratch capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (xs ys : List (StoredEntry n)) (nx ny budget C : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) (hsize : nx + ny ≤ C) :
    (run scratch capacity target blocks xs ys nx ny budget).2 ≤ bound scratch n C blocks := by
  induction blocks generalizing xs ys nx ny budget with
  | nil =>
    rw [run, bound]
    apply scope_cells
    intro fits left _
    split
    · exact StoredTerminalCells.budgeted_cells target xs ys nx ny left C hx hy hsize
    · exact Nat.zero_le _
  | cons b rest ih =>
    rw [run, bound]
    refine le_trans (scope_cells 8 (BudgetedSeparatorCheck.header capacity nx ny budget) _
      ((b.depth + 1) * (8 * (C + 1) + scratch) + bound scratch n C rest) ?_) ?_
    · intro fits left _
      split
      · apply BudgetedSeparatorCells.run_cells
        · intro j as bs na nb remaining ha hb hc
          exact ih as bs na nb remaining ha hb (by omega)
        · exact hx
        · exact hy
        · exact hsize
      · exact Nat.zero_le _
    · omega

def arrays (scratch capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) (budget : ℕ) : Execution Bool :=
  scope (4 * (left.size + right.size + 1)) (BudgetedSeparatorArrays.convert left right budget)
    fun lists remaining => run scratch capacity target blocks lists.1 lists.2
      left.size right.size remaining

theorem arrays_value (scratch capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) (budget : ℕ) :
    (arrays scratch capacity target blocks left right budget).1 =
      BudgetedSeparatorArrays.execute capacity target blocks left right budget := by
  simp only [arrays, scope_value, run_value, BudgetedSeparatorArrays.execute]

theorem arrays_cells (scratch capacity : ℕ) (target : ℤ) (blocks : List (Block n g))
    (left right : Array (StoredEntry n)) (budget C : ℕ) (hsize : left.size + right.size ≤ C) :
    (arrays scratch capacity target blocks left right budget).2 ≤
      4 * (C + 1) + bound scratch n C blocks := by
  apply le_trans (scope_cells _ _ _ (bound scratch n C blocks) ?_)
  · omega
  · intro lists remaining h
    obtain ⟨rfl, _, _⟩ := BudgetedSeparatorCall.value _ _ _ _ _ h
    exact run_cells scratch capacity target blocks left.toList right.toList
      left.size right.size remaining C (by simp) (by simp) hsize

theorem bound_le (scratch C depth : ℕ) (blocks : List (Block n g))
    (hd : ∀ b ∈ blocks, b.depth ≤ depth) :
    bound scratch n C blocks ≤ 8 + 72 * (n + 1) * (C + 1) +
      blocks.length * (8 + (depth + 1) * (8 * (C + 1) + scratch)) := by
  induction blocks with
  | nil => simp [bound]
  | cons b rest ih =>
    have hb := hd b (by simp)
    have hr := ih (fun d hd' => hd d (by simp [hd']))
    have hm := Nat.mul_le_mul_right (8 * (C + 1) + scratch) (Nat.add_le_add_right hb 1)
    simp only [bound, List.length_cons]
    nlinarith only [hr, hm]

end LowSpaceSubsetSum.BudgetedCheckerCells

end OAI
