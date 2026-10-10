import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedStreamContracts

namespace OAI

/-! # A watchdog for the complete stopped join

Each iteration reserves its own fixed control cost before invoking the prepaid
stream step. The reference allowance is used only in proofs; execution inspects
only its fuel, state, and remaining budget.
-/

namespace LowSpaceSubsetSum.BudgetedStoppedJoin

universe s t w
variable {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

local notation "State" => StreamJoin.State σ₁ σ₂ τ
local notation "Result" => StreamJoin.StoppedResult σ₁ σ₂ τ

def execute (step : State → ℕ → Option (State × ℕ) × ℕ) :
    ℕ → State → ℕ → Option (Result × ℕ) × ℕ
  | fuel, st, budget =>
    if 4 ≤ budget then
      match fuel with
      | 0 => (some (⟨st, 0⟩, budget - 4), 1)
      | fuel + 1 =>
        if st.done then (some (⟨st, 0⟩, budget - 4), 1) else
        let next := step st (budget - 4)
        match next.1 with
        | none => (none, next.2 + 2)
        | some (state, left) =>
          let rest := execute step fuel state left
          (rest.1.map (fun (out, remaining) => (⟨out.state, out.steps + 1⟩, remaining)),
            next.2 + rest.2 + 3)
    else (none, 1)

def reference (step : State → State) : ℕ → State → Result
  | 0, st => ⟨st, 0⟩
  | fuel + 1, st =>
    if st.done then ⟨st, 0⟩ else
    let out := reference step fuel (step st)
    ⟨out.state, out.steps + 1⟩

def allowance (step : State → State) (bill : State → ℕ) : ℕ → State → ℕ
  | 0, _ => 4
  | fuel + 1, st =>
    if st.done then 4 else 4 + bill st + allowance step bill fuel (step st)

theorem execute_value
    (step : State → ℕ → Option (State × ℕ) × ℕ) (pure : State → State)
    (hs : ∀ st b out left, (step st b).1 = some (out, left) → out = pure st ∧ left ≤ b)
    (fuel : ℕ) (st : State) (budget : ℕ) (out : Result) (left : ℕ)
    (h : (execute step fuel st budget).1 = some (out, left)) :
    out = reference pure fuel st ∧ left ≤ budget := by
  induction fuel generalizing st budget out left with
  | zero =>
    rw [execute] at h
    split at h
    · cases h
      exact ⟨rfl, Nat.sub_le _ _⟩
    · contradiction
  | succ fuel ih =>
    rw [execute] at h
    split at h
    next hb =>
      by_cases hd : st.done = true
      · simp only [hd, ↓reduceIte] at h
        cases h
        exact ⟨by simp only [reference, hd, ↓reduceIte], Nat.sub_le _ _⟩
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        cases hn : (step st (budget - 4)).1 with
        | none => simp only [hn] at h; contradiction
        | some p =>
          rcases p with ⟨next, remaining⟩
          have hv := hs st (budget - 4) next remaining hn
          simp only [hn] at h
          obtain ⟨p, hr, he⟩ := Option.map_eq_some_iff.mp h
          rcases p with ⟨rest, finalBudget⟩
          have hi := ih next remaining rest finalBudget hr
          cases he
          exact ⟨by simp only [reference, hd, Bool.false_eq_true, ↓reduceIte, ← hv.1, ← hi.1],
            hi.2.trans (hv.2.trans (Nat.sub_le _ _))⟩
    next _ => contradiction

theorem execute_work (step : State → ℕ → Option (State × ℕ) × ℕ)
    (hw : ∀ st b, (step st b).2 ≤ b + 1)
    (hs : ∀ st b out left, (step st b).1 = some (out, left) →
      left ≤ b ∧ (step st b).2 ≤ b - left)
    (fuel : ℕ) (st : State) (budget : ℕ) :
    (execute step fuel st budget).2 ≤ budget + 1 := by
  induction fuel generalizing st budget with
  | zero => rw [execute]; split <;> dsimp only <;> omega
  | succ fuel ih =>
    rw [execute]
    split
    next hb =>
      by_cases hd : st.done = true
      · simp only [hd, ↓reduceIte]; omega
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        have hn := hw st (budget - 4)
        cases he : (step st (budget - 4)).1 with
        | none => dsimp only; omega
        | some p =>
          rcases p with ⟨next, remaining⟩
          have hp := hs st (budget - 4) next remaining he
          have hi := ih next remaining
          dsimp only
          omega
    next _ => dsimp only; omega

theorem execute_spent (step : State → ℕ → Option (State × ℕ) × ℕ)
    (hs : ∀ st b out left, (step st b).1 = some (out, left) →
      left ≤ b ∧ (step st b).2 ≤ b - left)
    (fuel : ℕ) (st : State) (budget : ℕ) (out : Result) (left : ℕ)
    (h : (execute step fuel st budget).1 = some (out, left)) :
    left ≤ budget ∧ (execute step fuel st budget).2 ≤ budget - left := by
  induction fuel generalizing st budget out left with
  | zero =>
    rw [execute] at h ⊢
    split at h
    next hb =>
      simp only [hb, ↓reduceIte]
      cases h
      omega
    next _ => contradiction
  | succ fuel ih =>
    rw [execute] at h ⊢
    split at h
    next hb =>
      simp only [hb, ↓reduceIte] at h ⊢
      by_cases hd : st.done = true
      · simp only [hd, ↓reduceIte] at h ⊢
        cases h
        omega
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases hn : (step st (budget - 4)).1 with
        | none => simp only [hn] at h; contradiction
        | some p =>
          rcases p with ⟨next, remaining⟩
          have hp := hs st (budget - 4) next remaining hn
          simp only [hn] at h ⊢
          obtain ⟨p, hr, he⟩ := Option.map_eq_some_iff.mp h
          rcases p with ⟨rest, finalBudget⟩
          have hi := ih next remaining rest finalBudget hr
          cases he
          omega
    next _ => contradiction

theorem execute_complete
    (step : State → ℕ → Option (State × ℕ) × ℕ) (pure : State → State) (bill : State → ℕ)
    (hc : ∀ st b, bill st ≤ b → ∃ left, (step st b).1 = some (pure st, left))
    (hr : ∀ st b out left, (step st b).1 = some (out, left) → b ≤ left + bill st)
    (fuel : ℕ) (st : State) (budget : ℕ)
    (hb : allowance pure bill fuel st ≤ budget) :
    ∃ left, (execute step fuel st budget).1 = some (reference pure fuel st, left) := by
  induction fuel generalizing st budget with
  | zero =>
    have hb' : 4 ≤ budget := hb
    exact ⟨budget - 4, by simp only [execute, hb', ↓reduceIte, reference]⟩
  | succ fuel ih =>
    by_cases hd : st.done = true
    · simp only [allowance, hd, ↓reduceIte] at hb
      exact ⟨budget - 4, by simp only [execute, hb, hd, ↓reduceIte, reference]⟩
    · simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte] at hb
      have hb' : 4 ≤ budget := by omega
      obtain ⟨remaining, hn⟩ := hc st (budget - 4) (by omega)
      have hp := hr st (budget - 4) (pure st) remaining hn
      obtain ⟨finalBudget, he⟩ := ih (pure st) remaining (by omega)
      refine ⟨finalBudget, ?_⟩
      simp only [execute, hb', hd, Bool.false_eq_true, ↓reduceIte, hn, he, Option.map_some,
        reference]

/-- Telescoping the bills pays only for operations that the reference performs. -/
theorem allowance_potential (pure : State → State) (bill : State → ℕ)
    (potential : State → ℕ) (extra : ℕ)
    (hb : ∀ st, bill st + potential st ≤ potential (pure st) + extra)
    (fuel : ℕ) (st : State) :
    allowance pure bill fuel st + potential st ≤
      potential (reference pure fuel st).state + (extra + 4) * (reference pure fuel st).steps + 4 := by
  induction fuel generalizing st with
  | zero => simp only [allowance, reference, Nat.mul_zero, Nat.add_zero]; omega
  | succ fuel ih =>
    by_cases hd : st.done = true
    · simp only [allowance, reference, hd, ↓reduceIte, Nat.mul_zero, Nat.add_zero]; omega
    · have hs := hb st
      have hi := ih (pure st)
      simp only [allowance, reference, hd, Bool.false_eq_true, ↓reduceIte, Nat.mul_add, Nat.mul_one]
      omega

theorem execute_remaining
    (step : State → ℕ → Option (State × ℕ) × ℕ) (pure : State → State) (bill : State → ℕ)
    (hv : ∀ st b out left, (step st b).1 = some (out, left) → out = pure st)
    (hr : ∀ st b out left, (step st b).1 = some (out, left) → b ≤ left + bill st)
    (fuel : ℕ) (st : State) (budget : ℕ) (out : Result) (left : ℕ)
    (h : (execute step fuel st budget).1 = some (out, left)) :
    budget ≤ left + allowance pure bill fuel st := by
  induction fuel generalizing st budget out left with
  | zero =>
    rw [execute] at h
    split at h
    · cases h
      simp only [allowance]
      omega
    · contradiction
  | succ fuel ih =>
    rw [execute] at h
    split at h
    next hb =>
      by_cases hd : st.done = true
      · simp only [hd, ↓reduceIte] at h
        cases h
        simp only [allowance, hd, ↓reduceIte]
        omega
      · simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        cases hn : (step st (budget - 4)).1 with
        | none => simp only [hn] at h; contradiction
        | some p =>
          rcases p with ⟨next, remaining⟩
          have he := hv st (budget - 4) next remaining hn
          have hp := hr st (budget - 4) next remaining hn
          simp only [hn] at h
          obtain ⟨p, hrest, hmap⟩ := Option.map_eq_some_iff.mp h
          rcases p with ⟨rest, finalBudget⟩
          have hi := ih next remaining rest finalBudget hrest
          cases hmap
          simp only [allowance, hd, Bool.false_eq_true, ↓reduceIte, ← he]
          omega
    next _ => contradiction

end LowSpaceSubsetSum.BudgetedStoppedJoin

end OAI
