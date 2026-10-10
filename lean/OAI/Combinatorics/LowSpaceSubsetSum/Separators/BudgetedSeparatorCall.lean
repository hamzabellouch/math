import Mathlib.Tactic

namespace OAI

/-! # Reserving a known bound before a checker subroutine

The action is a thunk: its body is evaluated only inside the successful
budget branch. The returned counter includes the guard comparison.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorCall

variable {α : Type*}

abbrev Outcome (α : Type*) := Option (α × ℕ) × ℕ

def run (charge : ℕ) (action : Unit → α × ℕ) (budget : ℕ) : Outcome α :=
  if charge ≤ budget then
    let out := action ()
    (some (out.1, budget - charge), out.2 + 1)
  else (none, 1)

theorem insufficient (charge : ℕ) (action : Unit → α × ℕ) (budget : ℕ)
    (h : budget < charge) : run charge action budget = (none, 1) := by
  simp only [run, ite_eq_right (by omega : ¬charge ≤ budget)]

theorem complete (charge : ℕ) (action : Unit → α × ℕ) (budget : ℕ)
    (h : charge ≤ budget) :
    run charge action budget = (some ((action ()).1, budget - charge), (action ()).2 + 1) := by
  simp only [run, ite_eq_left h]

theorem value (charge : ℕ) (action : Unit → α × ℕ) (budget : ℕ)
    (a : α) (left : ℕ) (h : (run charge action budget).1 = some (a, left)) :
    a = (action ()).1 ∧ left = budget - charge ∧ charge ≤ budget := by
  unfold run at h
  split at h
  · cases h
    exact ⟨rfl, rfl, by assumption⟩
  · contradiction

theorem work (charge : ℕ) (action : Unit → α × ℕ) (budget : ℕ)
    (hcharge : (action ()).2 + 1 ≤ charge) :
    (run charge action budget).2 ≤ budget + 1 := by
  unfold run
  split <;> dsimp only <;> omega

theorem spent (charge : ℕ) (action : Unit → α × ℕ) (budget : ℕ)
    (hcharge : (action ()).2 + 1 ≤ charge)
    (a : α) (left : ℕ) (h : (run charge action budget).1 = some (a, left)) :
    left ≤ budget ∧ (run charge action budget).2 ≤ budget - left := by
  obtain ⟨_, rfl, hb⟩ := value charge action budget a left h
  rw [complete charge action budget hb]
  constructor <;> omega

end LowSpaceSubsetSum.BudgetedSeparatorCall

end OAI
