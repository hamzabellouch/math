import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStoppedLoop

namespace OAI

/-! # Constant-retention execution of the stopped join loop

Only the current state survives an iteration. The peak accumulator records
the temporary overlap between the old and returned state; no prior state is
stored in a continuation frame.
-/

namespace LowSpaceSubsetSum.BudgetedStoppedCells

universe s t w
variable {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}
local notation "State" => StreamJoin.State σ₁ σ₂ τ
local notation "Result" => StreamJoin.StoppedResult σ₁ σ₂ τ

def loop (step : State → ℕ → (Option (State × ℕ) × ℕ) × ℕ)
    (cells : State → ℕ) :
    ℕ → State → ℕ → ℕ → ℕ → ℕ → (Option (Result × ℕ) × ℕ) × ℕ
  | fuel, st, steps, budget, work, peak =>
    let live := max peak (cells st + 16)
    if 4 ≤ budget then
      match fuel with
      | 0 => ((some (⟨st, steps⟩, budget - 4), work + 1), live)
      | fuel + 1 =>
        if st.done then ((some (⟨st, steps⟩, budget - 4), work + 1), live) else
        let next := step st (budget - 4)
        let live := max live (cells st + next.2 + 16)
        match next.1.1 with
        | none => ((none, work + next.1.2 + 2), live)
        | some (state, left) =>
          loop step cells fuel state (steps + 1) left (work + next.1.2 + 3)
            (max live (cells st + cells state + 16))
    else ((none, work + 1), live)

theorem loop_value (step : State → ℕ → (Option (State × ℕ) × ℕ) × ℕ)
    (cells : State → ℕ) (fuel : ℕ) (st : State) (steps budget work peak : ℕ) :
    (loop step cells fuel st steps budget work peak).1 =
      BudgetedStoppedLoop.loop (fun st b => (step st b).1) fuel st steps budget work := by
  induction fuel generalizing st steps budget work peak with
  | zero => rw [loop, BudgetedStoppedLoop.loop]; split <;> rfl
  | succ fuel ih =>
    rw [loop, BudgetedStoppedLoop.loop]
    split
    · by_cases hd : st.done = true
      · simp only [hd, ↓reduceIte]
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        cases hn : (step st (budget - 4)).1.1 with
        | none => rfl
        | some p =>
          rcases p with ⟨state, left⟩
          exact ih _ _ _ _ _
    · rfl

theorem loop_cells (step : State → ℕ → (Option (State × ℕ) × ℕ) × ℕ)
    (cells : State → ℕ) (S T : ℕ)
    (hs : ∀ st, cells st ≤ S) (ht : ∀ st b, (step st b).2 ≤ T)
    (fuel : ℕ) (st : State) (steps budget work peak : ℕ) :
    (loop step cells fuel st steps budget work peak).2 ≤ max peak (2 * S + T + 32) := by
  induction fuel generalizing st steps budget work peak with
  | zero =>
    have h := hs st
    rw [loop]
    split <;> dsimp only <;> exact max_le_max le_rfl (by omega)
  | succ fuel ih =>
    have h := hs st
    have hk := ht st (budget - 4)
    rw [loop]
    split
    · by_cases hd : st.done = true
      · simp only [hd, ↓reduceIte]
        exact max_le_max le_rfl (by omega)
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        cases hn : (step st (budget - 4)).1.1 with
        | none => dsimp only; omega
        | some p =>
          rcases p with ⟨state, left⟩
          have ho := hs state
          have hi := ih state (steps + 1) left (work + (step st (budget - 4)).1.2 + 3)
            (max (max (max peak (cells st + 16))
              (cells st + (step st (budget - 4)).2 + 16)) (cells st + cells state + 16))
          exact hi.trans (by omega)
    · dsimp only
      exact max_le_max le_rfl (by omega)

def run (step : State → ℕ → (Option (State × ℕ) × ℕ) × ℕ) (cells : State → ℕ)
    (fuel : ℕ) (st : State) (budget : ℕ) := loop step cells fuel st 0 budget 0 0

theorem run_value (step : State → ℕ → (Option (State × ℕ) × ℕ) × ℕ) (cells : State → ℕ)
    (fuel : ℕ) (st : State) (budget : ℕ) :
    (run step cells fuel st budget).1 = BudgetedStoppedLoop.run (fun st b => (step st b).1) fuel st budget :=
  loop_value _ _ _ _ _ _ _ _

theorem run_cells (step : State → ℕ → (Option (State × ℕ) × ℕ) × ℕ)
    (cells : State → ℕ) (S T : ℕ)
    (hs : ∀ st, cells st ≤ S) (ht : ∀ st b, (step st b).2 ≤ T)
    (fuel : ℕ) (st : State) (budget : ℕ) :
    (run step cells fuel st budget).2 ≤ 2 * S + T + 32 := by
  simpa only [run, Nat.zero_max] using loop_cells step cells S T hs ht fuel st 0 budget 0 0

end LowSpaceSubsetSum.BudgetedStoppedCells

end OAI
