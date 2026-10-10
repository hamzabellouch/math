import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedOuterLoop

namespace OAI

/-! # Live cells of a tail replay with a prepaid inner callback

The callback may exhaust its remaining allowance. Its scratch trace is added
to the retained reader, current record and user state before the next tail
iteration, and failure drops all local continuations.
-/

namespace LowSpaceSubsetSum.BudgetedOuterCells

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def loop (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : α → τ → ℕ → (Option ((τ × Bool) × ℕ) × ℕ) × ℕ)
    (stateCells : σ → ℕ) (userCells : τ → ℕ) (recordCells : α → ℕ) :
    ℕ → σ → τ → ℕ → ℕ → ℕ → ℕ → ℕ →
      (Option (TieReplay.Result σ τ × ℕ) × ℕ) × ℕ
  | fuel, s, a, q, r, budget, work, peak =>
    let live := max peak (stateCells s + userCells a + 16)
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => ((some (⟨s, a, q, r, false, false⟩, left), work + 1), live)
      | fuel + 1 =>
        let fetched := read s
        let live := max live (stateCells s + userCells a + fetched.2 + 16)
        match fetched.1.1 with
        | none => ((some (⟨s, a, q + 1, r, true, false⟩, left), work + (fetched.1.2 + 5)), live)
        | some (x, s') =>
          let found := key x
          let live := max live
            (stateCells s + stateCells s' + userCells a + recordCells x + found.2 + 20)
          if found.1.1 = K then
            let out := report x a left
            let live := max live (stateCells s + stateCells s' + userCells a +
              recordCells x + out.2 + 24)
            match out.1.1 with
            | none => ((none, work + (fetched.1.2 + found.1.2 + out.1.2 + 8)), live)
            | some ((next, halt), remaining) =>
              let live := max live (stateCells s + stateCells s' + userCells a +
                userCells next + recordCells x + 24)
              if halt then
                ((some (⟨s', next, q + 1, r + 1, false, true⟩, remaining),
                  work + (fetched.1.2 + found.1.2 + out.1.2 + 8)), live)
              else loop charge read key K report stateCells userCells recordCells fuel s' next
                (q + 1) (r + 1) remaining (work + (fetched.1.2 + found.1.2 + out.1.2 + 8)) live
          else ((some (⟨s, a, q + 1, r, true, false⟩, left),
            work + (fetched.1.2 + found.1.2 + 6)), live)
    else ((none, work + 1), live)

theorem loop_value (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : α → τ → ℕ → (Option ((τ × Bool) × ℕ) × ℕ) × ℕ)
    (stateCells : σ → ℕ) (userCells : τ → ℕ) (recordCells : α → ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget work peak : ℕ) :
    (loop charge read key K report stateCells userCells recordCells fuel s a q r budget work peak).1 =
      BudgetedOuterLoop.loop charge (fun s => (read s).1) (fun x => (key x).1) K
        (fun x a b => (report x a b).1) fuel s a q r budget work := by
  induction fuel generalizing s a q r budget work peak with
  | zero => rw [loop, BudgetedOuterLoop.loop]; split <;> rfl
  | succ fuel ih =>
    rw [loop, BudgetedOuterLoop.loop]
    split
    · dsimp only
      cases hr : (read s).1.1 with
      | none => rfl
      | some p =>
        rcases p with ⟨x, s'⟩
        dsimp only
        split
        · cases hp : (report x a (budget - charge)).1.1 with
          | none => rfl
          | some p =>
            rcases p with ⟨⟨next, halt⟩, remaining⟩
            dsimp only
            split
            · rfl
            · exact ih _ _ _ _ _ _ _
        · rfl
    · rfl

theorem loop_cells (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : α → τ → ℕ → (Option ((τ × Bool) × ℕ) × ℕ) × ℕ)
    (stateCells : σ → ℕ) (userCells : τ → ℕ) (recordCells : α → ℕ)
    (S U X R L H : ℕ) (hs : ∀ s, stateCells s ≤ S) (hu : ∀ a, userCells a ≤ U)
    (hx : ∀ x, recordCells x ≤ X) (hr : ∀ s, (read s).2 ≤ R)
    (hk : ∀ x, (key x).2 ≤ L) (hp : ∀ x a b, (report x a b).2 ≤ H)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget work peak : ℕ) :
    (loop charge read key K report stateCells userCells recordCells fuel s a q r budget work peak).2 ≤
      max peak (2 * S + 2 * U + X + R + L + H + 64) := by
  induction fuel generalizing s a q r budget work peak with
  | zero =>
    have hs' := hs s
    have hu' := hu a
    rw [loop]
    split <;> dsimp only <;> exact max_le_max le_rfl (by omega)
  | succ fuel ih =>
    have hs' := hs s
    have hu' := hu a
    have hr' := hr s
    rw [loop]
    split
    · dsimp only
      cases he : (read s).1.1 with
      | none => dsimp only; omega
      | some p =>
        rcases p with ⟨x, s'⟩
        have hs'' := hs s'
        have hx' := hx x
        have hk' := hk x
        dsimp only
        split
        · have hp' := hp x a (budget - charge)
          cases ho : (report x a (budget - charge)).1.1 with
          | none => dsimp only; omega
          | some p =>
            rcases p with ⟨⟨next, halt⟩, remaining⟩
            have hu'' := hu next
            dsimp only
            split
            · dsimp only; omega
            · have hi := ih s' next (q + 1) (r + 1) remaining
                (work + ((read s).1.2 + (key x).1.2 + (report x a (budget - charge)).1.2 + 8))
                (max (max (max (max (max peak (stateCells s + userCells a + 16))
                  (stateCells s + userCells a + (read s).2 + 16))
                  (stateCells s + stateCells s' + userCells a + recordCells x + (key x).2 + 20))
                  (stateCells s + stateCells s' + userCells a + recordCells x +
                    (report x a (budget - charge)).2 + 24))
                  (stateCells s + stateCells s' + userCells a + userCells next + recordCells x + 24))
              exact hi.trans (by omega)
        · dsimp only; omega
    · dsimp only
      exact max_le_max le_rfl (by omega)

def run (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : α → τ → ℕ → (Option ((τ × Bool) × ℕ) × ℕ) × ℕ)
    (stateCells : σ → ℕ) (userCells : τ → ℕ) (recordCells : α → ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :=
  loop charge read key K report stateCells userCells recordCells fuel s a q r budget 0 0

theorem run_value (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : α → τ → ℕ → (Option ((τ × Bool) × ℕ) × ℕ) × ℕ)
    (stateCells : σ → ℕ) (userCells : τ → ℕ) (recordCells : α → ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :
    (run charge read key K report stateCells userCells recordCells fuel s a q r budget).1 =
      BudgetedOuterReplay.execute charge (fun s => (read s).1) (fun x => (key x).1) K
        (fun x a b => (report x a b).1) fuel s a q r budget := by
  rw [run, loop_value, BudgetedOuterLoop.loop_eq]
  simp only [Nat.zero_add]

theorem run_cells (charge : ℕ) (read : σ → (Option (α × σ) × ℕ) × ℕ)
    (key : α → (ℤ × ℕ) × ℕ) (K : ℤ)
    (report : α → τ → ℕ → (Option ((τ × Bool) × ℕ) × ℕ) × ℕ)
    (stateCells : σ → ℕ) (userCells : τ → ℕ) (recordCells : α → ℕ)
    (S U X R L H : ℕ) (hs : ∀ s, stateCells s ≤ S) (hu : ∀ a, userCells a ≤ U)
    (hx : ∀ x, recordCells x ≤ X) (hr : ∀ s, (read s).2 ≤ R)
    (hk : ∀ x, (key x).2 ≤ L) (hp : ∀ x a b, (report x a b).2 ≤ H)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :
    (run charge read key K report stateCells userCells recordCells fuel s a q r budget).2 ≤
      2 * S + 2 * U + X + R + L + H + 64 := by
  simpa only [run, Nat.zero_max] using
    loop_cells charge read key K report stateCells userCells recordCells S U X R L H
      hs hu hx hr hk hp fuel s a q r budget 0 0

end LowSpaceSubsetSum.BudgetedOuterCells

end OAI
