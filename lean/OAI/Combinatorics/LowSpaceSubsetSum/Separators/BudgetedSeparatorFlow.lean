import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorCall

namespace OAI

/-! # Sequencing the already charged checker operations

The enclosing node charge includes branch bookkeeping. These combinators
add only the work counters of their constituent charged operations.
-/

namespace LowSpaceSubsetSum.BudgetedSeparatorFlow

open BudgetedSeparatorCall

variable {α β : Type*}

def pure (a : α) (budget : ℕ) : Outcome α := (some (a, budget), 0)

def bind (first : Outcome α) (next : α → ℕ → Outcome β) : Outcome β :=
  match first.1 with
  | none => (none, first.2)
  | some (a, left) =>
    let out := next a left
    (out.1, first.2 + out.2)

def Account (budget : ℕ) (out : Outcome α) : Prop :=
  out.2 ≤ budget + 1 ∧
    ∀ a left, out.1 = some (a, left) → left ≤ budget ∧ out.2 ≤ budget - left

theorem pure_account (a : α) (budget : ℕ) : Account budget (pure a budget) := by
  constructor
  · simp [pure]
  · intro b left h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [pure]

theorem bind_account (first : Outcome α) (next : α → ℕ → Outcome β)
    (budget : ℕ) (hfirst : Account budget first)
    (hnext : ∀ a left, first.1 = some (a, left) → Account left (next a left)) :
    Account budget (bind first next) := by
  cases hf : first.1 with
  | none =>
    constructor
    · simpa only [bind, hf] using hfirst.1
    · intro a left h
      simp only [bind, hf] at h
      contradiction
  | some p =>
    rcases p with ⟨a, left⟩
    obtain ⟨hmleft, hmwork⟩ := hfirst.2 a left hf
    obtain ⟨hnwork, hnspent⟩ := hnext a left hf
    unfold Account
    simp only [bind, hf]
    constructor
    · omega
    · intro b rest h
      change (next a left).1 = some (b, rest) at h
      have hr := hnspent b rest h
      change rest ≤ budget ∧ first.2 + (next a left).2 ≤ budget - rest
      omega

theorem bind_eq_some (first : Outcome α) (next : α → ℕ → Outcome β)
    (b : β) (rest : ℕ) :
    (bind first next).1 = some (b, rest) ↔
      ∃ a left, first.1 = some (a, left) ∧ (next a left).1 = some (b, rest) := by
  cases hf : first.1 with
  | none => simp only [bind, hf, reduceCtorEq, false_and, exists_false]
  | some p =>
    rcases p with ⟨a, left⟩
    simp only [bind, hf, Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨a, left, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨a', left', ⟨rfl, rfl⟩, h⟩
      exact h

theorem bind_complete (first : Outcome α) (next : α → ℕ → Outcome β)
    (a : α) (left : ℕ) (b : β) (rest : ℕ)
    (hf : first.1 = some (a, left)) (hn : (next a left).1 = some (b, rest)) :
    (bind first next).1 = some (b, rest) :=
  (bind_eq_some first next b rest).mpr ⟨a, left, hf, hn⟩

end LowSpaceSubsetSum.BudgetedSeparatorFlow

end OAI
