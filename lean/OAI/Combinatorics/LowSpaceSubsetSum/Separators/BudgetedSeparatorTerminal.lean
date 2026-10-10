import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCall
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredEntryTerminal

namespace OAI

/-! # A prepaid terminal sort and weight match

The input lengths are cached by the preceding filter. The budget test uses
only those scalar fields; both sorts and the matching loop are evaluated
only after their full polynomial allowance has been reserved.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorTerminal

variable {n : ℕ}

def charge (n nx ny : ℕ) : ℕ := 64 * (n + 1) * (nx + ny + 1) + 1

def run (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget : ℕ) :
    BudgetedSeparatorCall.Outcome Bool :=
  BudgetedSeparatorCall.run (charge n nx ny)
    (fun _ => StoredEntryTerminal.run target xs ys) budget

theorem work (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny) :
    (run target xs ys nx ny budget).2 ≤ budget + 1 := by
  apply BudgetedSeparatorCall.work
  have h := StoredEntryTerminal.run_work target xs ys
  rw [hx, hy] at h
  exact Nat.add_le_add_right h 1

theorem value (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (hx : xs.length ≤ 2 ^ n) (hy : ys.length ≤ 2 ^ n)
    (result : Bool) (left : ℕ)
    (h : (run target xs ys nx ny budget).1 = some (result, left)) :
    result = (SeparatorTerminal.run StoredEntry.value StoredEntry.value target xs ys).accepted := by
  exact (BudgetedSeparatorCall.value _ _ _ _ _ h).1.trans
    (StoredEntryTerminal.run_value target xs ys hx hy)

theorem complete (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (h : charge n nx ny ≤ budget) :
    (run target xs ys nx ny budget).1 =
      some ((StoredEntryTerminal.run target xs ys).1, budget - charge n nx ny) := by
  rw [run, BudgetedSeparatorCall.complete _ _ _ h]

theorem spent (target : ℤ) (xs ys : List (StoredEntry n)) (nx ny budget : ℕ)
    (hx : xs.length = nx) (hy : ys.length = ny)
    (result : Bool) (left : ℕ)
    (h : (run target xs ys nx ny budget).1 = some (result, left)) :
    left ≤ budget ∧ (run target xs ys nx ny budget).2 ≤ budget - left := by
  apply BudgetedSeparatorCall.spent _ _ _ ?_ _ _ h
  have hw := StoredEntryTerminal.run_work target xs ys
  rw [hx, hy] at hw
  exact Nat.add_le_add_right hw 1

end LowSpaceSubsetSum.BudgetedSeparatorTerminal

end OAI
