import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedOuterCompletion

namespace OAI

namespace LowSpaceSubsetSum.BudgetedOuterReplay

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

theorem execute_remaining (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ)
    (pure : α → τ → τ × Bool) (bill : α → τ → ℕ)
    (hreport : ∀ x a b v left, (report x a b).1 = some (v, left) →
      v = pure x a ∧ b ≤ left + bill x a)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) (out : TieReplay.Result σ τ) (left : ℕ)
    (h : (execute charge read key K report fuel s a q r budget).1 = some (out, left)) :
    budget ≤ left + allowance charge (fun s => (read s).1) (fun x => (key x).1) K
      pure bill fuel s a := by
  induction fuel generalizing s a q r budget out left with
  | zero =>
    rw [execute] at h
    split at h
    next hb => cases h; simp only [allowance]; omega
    next _ => contradiction
  | succ fuel ih =>
    rw [execute] at h
    split at h
    next hb =>
      cases hr : (read s).1 with
      | none =>
        simp only [hr] at h
        cases h
        simp only [allowance, hr]
        omega
      | some p =>
        rcases p with ⟨x, s'⟩
        simp only [hr] at h
        split at h
        next hk =>
          cases hc : (report x a (budget - charge)).1 with
          | none => simp only [hc] at h; contradiction
          | some p =>
            rcases p with ⟨v, remaining⟩
            have hv := hreport x a (budget - charge) v remaining hc
            rcases v with ⟨next, halt⟩
            simp only [hc] at h
            split at h
            next hh =>
              cases h
              simp only [allowance, hr, hk, ↓reduceIte, ← hv.1, hh]
              omega
            next hh =>
              have hi := ih s' next (q + 1) (r + 1) remaining out left h
              simp only [allowance, hr, hk, ↓reduceIte, ← hv.1, hh, Bool.false_eq_true]
              omega
        next hk =>
          cases h
          simp only [allowance, hr, hk, ↓reduceIte]
          omega
    next _ => contradiction

end LowSpaceSubsetSum.BudgetedOuterReplay

end OAI
