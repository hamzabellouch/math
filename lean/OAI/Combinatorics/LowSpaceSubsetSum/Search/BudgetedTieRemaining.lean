import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieOuter
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedOuterRemaining

namespace OAI

namespace LowSpaceSubsetSum.BudgetedTieStep

universe u v s t w
variable {α : Type u} {β : Type v} {σ : Type s} {τ : Type t}

theorem execute_remaining (charge copyCharge : ℕ) (read : σ → Option (β × σ) × ℕ)
    (key : β → ℤ × ℕ) (K : ℤ) (report : α → β → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array β) (saved : σ) (long : Bool) (fuel : ℕ)
    (x : α) (st : TieGroup.State σ τ) (budget : ℕ) (out : TieGroup.State σ τ × Bool) (left : ℕ)
    (h : (execute charge copyCharge read key K report clone buffer saved long fuel x st budget).1 =
      some (out, left)) :
    budget ≤ left + bill charge copyCharge read key K report clone buffer saved long fuel x st := by
  rw [execute] at h
  split at h
  next hb =>
    obtain ⟨pair, hi, he⟩ := Option.map_eq_some_iff.mp h
    rcases pair with ⟨inner, remaining⟩
    have hr := BudgetedJoinOne.execute_remaining charge copyCharge read key K (report x) clone
      buffer saved long fuel st.user (budget - 6) inner remaining hi
    have hv := (BudgetedJoinOne.execute_value charge copyCharge read key K (report x) clone
      buffer saved long fuel st.user (budget - 6) inner remaining hi).1
    rw [hv] at hr
    cases he
    unfold bill
    omega
  next _ => contradiction

end LowSpaceSubsetSum.BudgetedTieStep

namespace LowSpaceSubsetSum.BudgetedTieOuter

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

theorem execute_remaining (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ)
    (out : TieReplay.Result σ₁ (TieGroup.State σ₂ τ)) (left : ℕ)
    (h : (execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st budget).1 = some (out, left)) :
    budget ≤ left + allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st := by
  apply BudgetedOuterReplay.execute_remaining outerCharge read₁ key₁ K _
    (fun x st => (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂ x st).1)
    (BudgetedTieStep.bill charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂)
    _ fuel₁ s₁ st 0 0 budget out left h
  intro x a b value remaining hv
  exact ⟨(BudgetedTieStep.execute_value charge copyCharge read₂ key₂ K report clone
    buffer saved long fuel₂ x a b value remaining hv).1,
    BudgetedTieStep.execute_remaining charge copyCharge read₂ key₂ K report clone
      buffer saved long fuel₂ x a b value remaining hv⟩

end LowSpaceSubsetSum.BudgetedTieOuter

end OAI
