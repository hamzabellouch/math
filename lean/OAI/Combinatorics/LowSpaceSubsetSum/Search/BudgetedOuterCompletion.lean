import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedOuterReplay

namespace OAI

/-! # Sufficient prepaid allowance for nested outer replay

The analysis charges the actual callback at each consumed occurrence. Unused
advertised fuel is absent from the allowance. `allowance` is proof-only.
-/

namespace LowSpaceSubsetSum.BudgetedOuterReplay

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def allowance (charge : ℕ) (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (bill : α → τ → ℕ) : ℕ → σ → τ → ℕ
  | 0, _, _ => charge
  | fuel + 1, s, a => match read s with
    | none => charge
    | some (x, s') => if key x = K then
        let out := report x a
        if out.2 then charge + bill x a
        else charge + bill x a + allowance charge read key K report bill fuel s' out.1
      else charge

theorem execute_complete (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ)
    (pure : α → τ → τ × Bool) (bill : α → τ → ℕ)
    (hreport : ∀ x a b, bill x a ≤ b → ∃ left,
      (report x a b).1 = some (pure x a, left) ∧ b ≤ left + bill x a)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (hbudget : allowance charge (fun s => (read s).1) (fun x => (key x).1) K
      pure bill fuel s a ≤ budget) :
    ∃ left, (execute charge read key K report fuel s a q r budget).1 =
      some (TieReplay.runAcc (fun s => (read s).1) (fun x => (key x).1) K pure fuel s a q r, left) := by
  induction fuel generalizing s a q r budget with
  | zero =>
    change charge ≤ budget at hbudget
    refine ⟨budget - charge, ?_⟩
    rw [execute, ite_eq_left hbudget]
    rfl
  | succ fuel ih =>
    rw [allowance] at hbudget
    cases hr : (read s).1 with
    | none =>
      simp only [hr] at hbudget
      refine ⟨budget - charge, ?_⟩
      rw [execute, ite_eq_left hbudget]
      simp only [hr, TieReplay.runAcc]
    | some p =>
      rcases p with ⟨x, s'⟩
      simp only [hr] at hbudget
      by_cases hk : (key x).1 = K
      · simp only [hk, ↓reduceIte] at hbudget
        by_cases hh : (pure x a).2 = true
        · simp only [hh, ↓reduceIte] at hbudget
          have hb : charge ≤ budget := by omega
          obtain ⟨left, hp, _⟩ := hreport x a (budget - charge) (by omega)
          refine ⟨left, ?_⟩
          rw [execute, ite_eq_left hb]
          simp only [hr, hk, ↓reduceIte, hp]
          cases he : pure x a with
          | mk next halt =>
            simp only [he] at hh ⊢
            simp only [hh, ↓reduceIte, TieReplay.runAcc, hr, hk, he]
        · simp only [hh, Bool.false_eq_true, ↓reduceIte] at hbudget
          have hb : charge ≤ budget := by omega
          obtain ⟨left, hp, hl⟩ := hreport x a (budget - charge) (by omega)
          have ht : allowance charge (fun s => (read s).1) (fun x => (key x).1) K
              pure bill fuel s' (pure x a).1 ≤ left := by omega
          obtain ⟨remaining, hi⟩ := ih s' (pure x a).1 (q + 1) (r + 1) left ht
          refine ⟨remaining, ?_⟩
          rw [execute, ite_eq_left hb]
          simp only [hr, hk, ↓reduceIte, hp]
          cases he : pure x a with
          | mk next halt =>
            simp only [he] at hh hi ⊢
            simp only [hh, Bool.false_eq_true, ↓reduceIte, TieReplay.runAcc, hr, hk, he]
            exact hi
      · simp only [hk, ↓reduceIte] at hbudget
        refine ⟨budget - charge, ?_⟩
        rw [execute, ite_eq_left hbudget]
        simp only [hr, hk, ↓reduceIte, TieReplay.runAcc]

/-- Callback charges telescope through the actual callback state. -/
theorem allowance_le_potential (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (bill : α → τ → ℕ) (potential : τ → ℕ)
    (charge extra : ℕ)
    (hbill : ∀ x a, bill x a + potential a ≤ potential (report x a).1 + extra)
    (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    allowance charge read key K report bill fuel s a + potential a + (charge + extra) * q ≤
      (charge + extra) * (TieReplay.runAcc read key K report fuel s a q r).queries +
        potential (TieReplay.runAcc read key K report fuel s a q r).state + charge := by
  induction fuel generalizing s a q r with
  | zero => simp only [allowance, TieReplay.runAcc]; omega
  | succ fuel ih =>
    rw [allowance, TieReplay.runAcc]
    cases hr : read s with
    | none => simp only [Nat.mul_add, Nat.mul_one]; omega
    | some p =>
      rcases p with ⟨x, s'⟩
      try dsimp only
      by_cases hk : key x = K
      · simp only [hk, ↓reduceIte]
        have hb := hbill x a
        by_cases hh : (report x a).2 = true
        · simp only [hh, ↓reduceIte, Nat.mul_add, Nat.mul_one]
          omega
        · simp only [hh, Bool.false_eq_true, ↓reduceIte]
          have hi := ih s' (report x a).1 (q + 1) (r + 1)
          simp only [Nat.mul_add, Nat.mul_one] at hi
          omega
      · simp only [hk, ↓reduceIte, Nat.mul_add, Nat.mul_one]
        omega

end LowSpaceSubsetSum.BudgetedOuterReplay

end OAI
