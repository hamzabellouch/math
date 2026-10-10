import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStoppedJoin

namespace OAI

/-! # Tail-recursive execution of the prepaid stopped join

The loop keeps the completed-step and measured-work counters in its state.
No frame containing a prior cursor survives a recursive call.
-/

namespace LowSpaceSubsetSum.BudgetedStoppedLoop

universe s t w
variable {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}
local notation "State" => StreamJoin.State σ₁ σ₂ τ
local notation "Result" => StreamJoin.StoppedResult σ₁ σ₂ τ

def shift (steps : ℕ) (out : Result) : Result := ⟨out.state, out.steps + steps⟩

def loop (step : State → ℕ → Option (State × ℕ) × ℕ) :
    ℕ → State → ℕ → ℕ → ℕ → Option (Result × ℕ) × ℕ
  | fuel, st, steps, budget, work =>
    if 4 ≤ budget then
      match fuel with
      | 0 => (some (⟨st, steps⟩, budget - 4), work + 1)
      | fuel + 1 =>
        if st.done then (some (⟨st, steps⟩, budget - 4), work + 1) else
        let next := step st (budget - 4)
        match next.1 with
        | none => (none, work + next.2 + 2)
        | some (state, left) => loop step fuel state (steps + 1) left (work + next.2 + 3)
    else (none, work + 1)

theorem loop_eq (step : State → ℕ → Option (State × ℕ) × ℕ)
    (fuel : ℕ) (st : State) (steps budget work : ℕ) :
    loop step fuel st steps budget work =
      ((BudgetedStoppedJoin.execute step fuel st budget).1.map (fun (out, left) => (shift steps out, left)),
        work + (BudgetedStoppedJoin.execute step fuel st budget).2) := by
  induction fuel generalizing st steps budget work with
  | zero =>
    rw [loop, BudgetedStoppedJoin.execute]
    split <;> simp only [Option.map_some, Option.map_none, shift, Nat.zero_add]
  | succ fuel ih =>
    rw [loop, BudgetedStoppedJoin.execute]
    split
    next hb =>
      by_cases hd : st.done = true
      · simp only [hd, ↓reduceIte, Option.map_some, shift, Nat.zero_add]
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        cases hn : (step st (budget - 4)).1 with
        | none => simp only [Option.map_none, Nat.add_assoc]
        | some p =>
          rcases p with ⟨next, remaining⟩
          dsimp only
          rw [ih]
          simp only [Option.map_map, Function.comp_def, shift, Nat.add_assoc]
          apply Prod.ext
          · apply congrArg (fun f => (BudgetedStoppedJoin.execute step fuel next remaining).1.map f)
            funext p
            rcases p with ⟨out, left⟩
            simp only
            congr 2
            omega
          · omega
    next _ => rfl

def run (step : State → ℕ → Option (State × ℕ) × ℕ)
    (fuel : ℕ) (st : State) (budget : ℕ) := loop step fuel st 0 budget 0

theorem run_eq (step : State → ℕ → Option (State × ℕ) × ℕ)
    (fuel : ℕ) (st : State) (budget : ℕ) :
    run step fuel st budget = BudgetedStoppedJoin.execute step fuel st budget := by
  rw [run, loop_eq]
  simp only [shift, Nat.add_zero, Nat.zero_add]
  change ((BudgetedStoppedJoin.execute step fuel st budget).1.map id, _) = _
  apply Prod.ext
  · exact Option.map_id'
  · rfl

end LowSpaceSubsetSum.BudgetedStoppedLoop

end OAI
