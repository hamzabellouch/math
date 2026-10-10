import OAI.Combinatorics.LowSpaceSubsetSum.Streams.MeasuredSortSpace
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorTerminal

namespace OAI

/-! # The terminal check with exact sort-and-match storage accounting

The record payloads stay in the retained dictionary arrays. List spines and
sort continuations are accounted explicitly; both sorts execute in order.
The matching loop is tail recursive and retains two list cursors.
-/

namespace LowSpaceSubsetSum.StoredTerminalCells

variable {n : ℕ}

private def lengthAcc {α : Type*} : List α → ℕ → ℕ → ℕ × ℕ
  | [], count, work => (count, work + 1)
  | _ :: xs, count, work => lengthAcc xs (count + 1) (work + 2)

private theorem lengthAcc_eq {α : Type*} (xs : List α) (count work : ℕ) :
    lengthAcc xs count work = (count + xs.length, work + 2 * xs.length + 1) := by
  induction xs generalizing count work with
  | nil => simp [lengthAcc]
  | cons x xs ih => simp only [lengthAcc, ih, List.length_cons]; congr 1 <;> omega

def run (target : ℤ) (xs ys : List (StoredEntry n)) : (Bool × ℕ) × ℕ :=
  let nx := lengthAcc xs 0 0
  let ny := lengthAcc ys 0 0
  if xs.isEmpty || ys.isEmpty then ((false, nx.2 + ny.2 + 3), 8) else
    let left := MeasuredSortSpace.run StoredEntryTerminal.leftCompare n xs
    let right := MeasuredSortSpace.run (StoredEntryTerminal.rightCompare target) n ys
    let out := StoredEntryTerminal.findAcc target (nx.1 + ny.1 + 1) left.1.1 right.1.1 0
    ((out.1, nx.2 + ny.2 + left.1.2 + right.1.2 + out.2 + 5),
      8 * (xs.length + ys.length + 1) + max left.2 right.2)

theorem run_value (target : ℤ) (xs ys : List (StoredEntry n)) :
    (run target xs ys).1 = StoredEntryTerminal.run target xs ys := by
  rw [StoredEntryTerminal.run_expanded]
  simp only [run, lengthAcc_eq, Nat.zero_add, MeasuredSortSpace.run_value]
  by_cases he : (xs.isEmpty || ys.isEmpty) = true
  · simp only [he, ↓reduceIte]
  · simp only [he, Bool.false_eq_true, ↓reduceIte]

theorem run_cells (target : ℤ) (xs ys : List (StoredEntry n)) :
    (run target xs ys).2 ≤ 64 * (n + 1) * (xs.length + ys.length + 1) := by
  have hl := MeasuredSortSpace.run_cells (StoredEntryTerminal.leftCompare (n := n)) n xs
  have hr := MeasuredSortSpace.run_cells (StoredEntryTerminal.rightCompare (n := n) target) n ys
  have hleft := hl.trans (Nat.mul_le_mul_left (32 * (n + 1))
    (show xs.length + 1 ≤ xs.length + ys.length + 1 by omega))
  have hright := hr.trans (Nat.mul_le_mul_left (32 * (n + 1))
    (show ys.length + 1 ≤ xs.length + ys.length + 1 by omega))
  have hm := max_le hleft hright
  simp only [run]
  split
  · dsimp only
    nlinarith only [Nat.zero_le n, Nat.zero_le xs.length, Nat.zero_le ys.length]
  · dsimp only
    nlinarith only [hm, Nat.zero_le (n * (xs.length + ys.length + 1))]

/-- No terminal allocation occurs before its guard succeeds. -/
def budgeted (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget : ℕ) :
    BudgetedSeparatorCall.Outcome Bool × ℕ :=
  if BudgetedSeparatorTerminal.charge n nx ny ≤ budget then
    let out := run target xs ys
    ((some (out.1.1, budget - BudgetedSeparatorTerminal.charge n nx ny), out.1.2 + 1),
      out.2 + 8)
  else ((none, 1), 8)

theorem budgeted_value (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget : ℕ) :
    (budgeted target xs ys nx ny budget).1 =
      BudgetedSeparatorTerminal.run target xs ys nx ny budget := by
  simp only [budgeted, BudgetedSeparatorTerminal.run, BudgetedSeparatorCall.run]
  split <;> simp_all only [run_value]

theorem budgeted_cells (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget C : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) (hsize : nx + ny ≤ C) :
    (budgeted target xs ys nx ny budget).2 ≤ 72 * (n + 1) * (C + 1) := by
  have hr := run_cells target xs ys
  rw [hx, hy] at hr
  have hm := hr.trans (Nat.mul_le_mul_left (64 * (n + 1)) (by omega : nx + ny + 1 ≤ C + 1))
  simp only [budgeted]
  split <;> dsimp only <;>
    nlinarith only [hm, Nat.zero_le n, Nat.zero_le C, Nat.zero_le (n * C)]

end LowSpaceSubsetSum.StoredTerminalCells

end OAI
