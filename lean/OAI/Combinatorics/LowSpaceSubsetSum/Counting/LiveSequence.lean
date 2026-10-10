import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCells

namespace OAI

/-! # Sequencing with the returned object retained by the continuation -/

namespace LowSpaceSubsetSum.LiveSequence

open BudgetedSeparatorCells

variable {α β : Type*}

def run (keep : α → ℕ) (first : Execution α) (next : α → ℕ → Execution β) : Execution β :=
  match first.1.1 with
  | none => ((none, first.1.2), first.2)
  | some (a, left) =>
    let out := next a left
    ((out.1.1, first.1.2 + out.1.2), max first.2 (keep a + out.2))

theorem value (keep : α → ℕ) (first : Execution α) (next : α → ℕ → Execution β) :
    (run keep first next).1 = BudgetedSeparatorFlow.bind first.1 (fun a b => (next a b).1) := by
  simp only [run, BudgetedSeparatorFlow.bind]
  split <;> simp_all only

theorem cells (keep : α → ℕ) (first : Execution α) (next : α → ℕ → Execution β)
    (L R K : ℕ) (hfirst : first.2 ≤ L)
    (hkeep : ∀ a b, first.1.1 = some (a, b) → keep a ≤ R)
    (hnext : ∀ a b, first.1.1 = some (a, b) → (next a b).2 ≤ K) :
    (run keep first next).2 ≤ max L (R + K) := by
  unfold run
  split
  · exact hfirst.trans (le_max_left _ _)
  next a b h =>
    exact max_le_max hfirst (Nat.add_le_add (hkeep a b h) (hnext a b h))

end LowSpaceSubsetSum.LiveSequence

end OAI
