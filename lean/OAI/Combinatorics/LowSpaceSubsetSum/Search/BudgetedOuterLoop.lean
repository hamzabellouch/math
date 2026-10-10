import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedOuterReplay
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedReplayLoops

namespace OAI

namespace LowSpaceSubsetSum.BudgetedOuterLoop

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def loop (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ) :
    ℕ → σ → τ → ℕ → ℕ → ℕ → ℕ → Option (TieReplay.Result σ τ × ℕ) × ℕ
  | fuel, s, a, q, r, budget, work =>
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => (some (⟨s, a, q, r, false, false⟩, left), work + 1)
      | fuel + 1 =>
        let fetched := read s
        match fetched.1 with
        | none => (some (⟨s, a, q + 1, r, true, false⟩, left), work + (fetched.2 + 5))
        | some (x, s') =>
          let found := key x
          if found.1 = K then
            let reported := report x a left
            match reported.1 with
            | none => (none, work + (fetched.2 + found.2 + reported.2 + 8))
            | some ((next, halt), remaining) =>
              if halt then
                (some (⟨s', next, q + 1, r + 1, false, true⟩, remaining),
                  work + (fetched.2 + found.2 + reported.2 + 8))
              else loop charge read key K report fuel s' next (q + 1) (r + 1) remaining
                (work + (fetched.2 + found.2 + reported.2 + 8))
          else (some (⟨s, a, q + 1, r, true, false⟩, left), work + (fetched.2 + found.2 + 6))
    else (none, work + 1)

theorem loop_eq (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget work : ℕ) :
    loop charge read key K report fuel s a q r budget work =
      ((BudgetedOuterReplay.execute charge read key K report fuel s a q r budget).1,
        work + (BudgetedOuterReplay.execute charge read key K report fuel s a q r budget).2) := by
  induction fuel generalizing s a q r budget work with
  | zero => rw [loop, BudgetedOuterReplay.execute]; split <;> rfl
  | succ fuel ih =>
    rw [loop, BudgetedOuterReplay.execute]
    split
    · dsimp only
      cases hr : (read s).1 with
      | none => dsimp only
      | some p =>
        rcases p with ⟨x, s'⟩
        dsimp only
        split
        · cases hc : (report x a (budget - charge)).1 with
          | none => dsimp only
          | some p =>
            rcases p with ⟨⟨next, halt⟩, remaining⟩
            dsimp only
            split
            · rfl
            · rw [ih]
              simp only [Nat.add_assoc]
        · rfl
    · rfl

def execute (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :=
  loop charge read key K report fuel s a q r budget 0

@[csimp] theorem execute_eq : @BudgetedOuterReplay.execute.{u, v, w} = @execute.{u, v, w} := by
  funext α σ τ charge read key K report fuel s a q r budget
  rw [execute, loop_eq]
  simp only [Nat.zero_add]

end LowSpaceSubsetSum.BudgetedOuterLoop

end OAI
