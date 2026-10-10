import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedTieStep
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedOuterLoop

namespace OAI

/-! # Prepaid outer traversal of a Cartesian tie group -/

namespace LowSpaceSubsetSum.BudgetedTieOuter

universe u v s t w
variable {α : Type u} {β : Type v} {σ₁ : Type s} {σ₂ : Type t} {τ : Type w}

def execute (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ) :=
  BudgetedOuterReplay.execute outerCharge read₁ key₁ K
    (BudgetedTieStep.execute charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂)
    fuel₁ s₁ st 0 0 budget

def reference (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) :=
  CountedReplay.run read₁ key₁ K
    (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂) fuel₁ s₁ st

theorem execute_value (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ)
    (out : TieReplay.Result σ₁ (TieGroup.State σ₂ τ)) (left : ℕ)
    (h : (execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st budget).1 = some (out, left)) :
    out = (reference read₁ key₁ read₂ key₂ K report clone buffer saved long fuel₁ fuel₂ s₁ st).1 ∧
      left ≤ budget := by
  have hv := BudgetedOuterReplay.execute_value outerCharge read₁ key₁ K _
    (fun x st => (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂ x st).1)
    (BudgetedTieStep.execute_value charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂)
    fuel₁ s₁ st 0 0 budget out left h
  simpa only [reference, CountedReplay.run_value, TieReplay.run] using hv

theorem execute_work
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (R₁ L₁ R₂ L₂ C outerCharge charge copyCharge : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hk₁ : ∀ x, (key₁ x).2 ≤ L₁)
    (hr₂ : ∀ s, (read₂ s).2 ≤ R₂) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hc : ∀ x y a, (report x y a).2 ≤ C)
    (houter : R₁ + L₁ + 8 ≤ outerCharge)
    (hcharge : max R₂ 4 + L₂ + C + 8 ≤ charge) (hcopy : ∀ s, (clone s).2 ≤ copyCharge)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ) :
    (execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st budget).2 ≤ budget + 1 := by
  exact BudgetedOuterReplay.execute_work read₁ key₁ K _ R₁ L₁ outerCharge hr₁ hk₁ houter
    (BudgetedTieStep.execute_work read₂ key₂ K report clone R₂ L₂ C charge copyCharge
      hr₂ hk₂ hc hcharge hcopy buffer saved long fuel₂)
    (BudgetedTieStep.execute_spent read₂ key₂ K report clone R₂ L₂ C charge copyCharge
      hr₂ hk₂ hc hcharge hcopy buffer saved long fuel₂) fuel₁ s₁ st 0 0 budget

theorem execute_spent
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (R₁ L₁ R₂ L₂ C outerCharge charge copyCharge : ℕ)
    (hr₁ : ∀ s, (read₁ s).2 ≤ R₁) (hk₁ : ∀ x, (key₁ x).2 ≤ L₁)
    (hr₂ : ∀ s, (read₂ s).2 ≤ R₂) (hk₂ : ∀ y, (key₂ y).2 ≤ L₂)
    (hc : ∀ x y a, (report x y a).2 ≤ C)
    (houter : R₁ + L₁ + 8 ≤ outerCharge)
    (hcharge : max R₂ 4 + L₂ + C + 8 ≤ charge) (hcopy : ∀ s, (clone s).2 ≤ copyCharge)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ)
    (out : TieReplay.Result σ₁ (TieGroup.State σ₂ τ)) (left : ℕ)
    (h : (execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st budget).1 = some (out, left)) :
    left ≤ budget ∧ (execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st budget).2 ≤ budget - left := by
  exact BudgetedOuterReplay.execute_spent read₁ key₁ K _ R₁ L₁ outerCharge hr₁ hk₁ houter
    (BudgetedTieStep.execute_spent read₂ key₂ K report clone R₂ L₂ C charge copyCharge
      hr₂ hk₂ hc hcharge hcopy buffer saved long fuel₂) fuel₁ s₁ st 0 0 budget out left h

def potential (charge copyCharge : ℕ) (st : TieGroup.State σ₂ τ) : ℕ :=
  charge * st.queries + copyCharge * st.restores

def allowance (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) : ℕ :=
  BudgetedOuterReplay.allowance outerCharge (fun s => (read₁ s).1) (fun x => (key₁ x).1) K
    (fun x st => (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂ x st).1)
    (BudgetedTieStep.bill charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂)
    fuel₁ s₁ st

theorem allowance_le (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) :
    allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st ≤
    (outerCharge + 2 * charge + 12) *
      (reference read₁ key₁ read₂ key₂ K report clone buffer saved long fuel₁ fuel₂ s₁ st).1.queries +
    potential charge copyCharge
      (reference read₁ key₁ read₂ key₂ K report clone buffer saved long fuel₁ fuel₂ s₁ st).1.state +
    outerCharge := by
  have hbill : ∀ x a, BudgetedTieStep.bill charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂ x a +
      potential charge copyCharge a ≤
      potential charge copyCharge
        (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂ x a).1.1 +
      (2 * charge + 12) := by
    intro x a
    cases long <;> simp only [BudgetedTieStep.bill, potential, CountedTieGroup.step,
      Bool.false_eq_true, ↓reduceIte, Nat.mul_add, Nat.mul_one, Nat.add_zero] <;> omega
  have hp := BudgetedOuterReplay.allowance_le_potential (fun s => (read₁ s).1)
    (fun x => (key₁ x).1) K
    (fun x st => (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂ x st).1)
    (BudgetedTieStep.bill charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂)
    (potential charge copyCharge) outerCharge (2 * charge + 12) hbill fuel₁ s₁ st 0 0
  have href := CountedReplay.run_value read₁ key₁ K
    (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂) fuel₁ s₁ st
  simp only [TieReplay.run] at href
  rw [← href] at hp
  change allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
    fuel₁ fuel₂ s₁ st + potential charge copyCharge st + (outerCharge + (2 * charge + 12)) * 0 ≤
    (outerCharge + (2 * charge + 12)) *
      (reference read₁ key₁ read₂ key₂ K report clone buffer saved long fuel₁ fuel₂ s₁ st).1.queries +
    potential charge copyCharge
      (reference read₁ key₁ read₂ key₂ K report clone buffer saved long fuel₁ fuel₂ s₁ st).1.state +
    outerCharge at hp
  simp only [Nat.mul_zero, Nat.add_zero] at hp
  simpa only [Nat.add_assoc] using (Nat.le_add_right _ _).trans hp

theorem execute_complete (outerCharge charge copyCharge : ℕ)
    (read₁ : σ₁ → Option (α × σ₁) × ℕ) (key₁ : α → ℤ × ℕ)
    (read₂ : σ₂ → Option (β × σ₂) × ℕ) (key₂ : β → ℤ × ℕ) (K : ℤ)
    (report : α → β → τ → (τ × Bool) × ℕ) (clone : σ₂ → σ₂ × ℕ)
    (buffer : Array β) (saved : σ₂) (long : Bool) (fuel₁ fuel₂ : ℕ)
    (s₁ : σ₁) (st : TieGroup.State σ₂ τ) (budget : ℕ)
    (hb : allowance outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st ≤ budget) :
    ∃ left, (execute outerCharge charge copyCharge read₁ key₁ read₂ key₂ K report clone buffer saved long
      fuel₁ fuel₂ s₁ st budget).1 =
      some ((reference read₁ key₁ read₂ key₂ K report clone buffer saved long fuel₁ fuel₂ s₁ st).1, left) := by
  have h := BudgetedOuterReplay.execute_complete outerCharge read₁ key₁ K _
    (fun x st => (CountedTieGroup.step read₂ key₂ K report clone buffer saved long fuel₂ x st).1)
    (BudgetedTieStep.bill charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂)
    (BudgetedTieStep.execute_complete charge copyCharge read₂ key₂ K report clone buffer saved long fuel₂)
    fuel₁ s₁ st 0 0 budget hb
  simpa only [execute, reference, CountedReplay.run_value, TieReplay.run] using h

end LowSpaceSubsetSum.BudgetedTieOuter

end OAI
