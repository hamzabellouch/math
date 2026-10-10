import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedJoinOne

namespace OAI

/-! # Outer replay with a budgeted inner callback

The fixed charge covers one outer read/key step. A callback receives the
remaining allowance and returns its unspent part. This is the control used
when one outer occurrence triggers a buffered Cartesian replay.
-/

namespace LowSpaceSubsetSum.BudgetedOuterReplay

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def execute (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ) :
    ℕ → σ → τ → ℕ → ℕ → ℕ → Option (TieReplay.Result σ τ × ℕ) × ℕ
  | fuel, s, a, q, r, budget =>
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => (some (⟨s, a, q, r, false, false⟩, left), 1)
      | fuel + 1 =>
        let fetched := read s
        match fetched.1 with
        | none => (some (⟨s, a, q + 1, r, true, false⟩, left), fetched.2 + 5)
        | some (x, s') =>
          let found := key x
          if found.1 = K then
            let reported := report x a left
            match reported.1 with
            | none => (none, fetched.2 + found.2 + reported.2 + 8)
            | some ((next, halt), remaining) =>
              if halt then
                (some (⟨s', next, q + 1, r + 1, false, true⟩, remaining),
                  fetched.2 + found.2 + reported.2 + 8)
              else
                let rest := execute charge read key K report fuel s' next (q + 1) (r + 1) remaining
                (rest.1, fetched.2 + found.2 + reported.2 + 8 + rest.2)
          else (some (⟨s, a, q + 1, r, true, false⟩, left), fetched.2 + found.2 + 6)
    else (none, 1)

theorem execute_value (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ) (pure : α → τ → τ × Bool)
    (hreport : ∀ x a b v left, (report x a b).1 = some (v, left) → v = pure x a ∧ left ≤ b)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) (out : TieReplay.Result σ τ) (left : ℕ)
    (h : (execute charge read key K report fuel s a q r budget).1 = some (out, left)) :
    out = TieReplay.runAcc (fun s => (read s).1) (fun x => (key x).1) K pure fuel s a q r ∧
      left ≤ budget := by
  induction fuel generalizing s a q r budget out left with
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
      cases hr : (read s).1 with
      | none =>
        simp only [hr] at h
        cases h
        exact ⟨by simp only [TieReplay.runAcc, hr], Nat.sub_le _ _⟩
      | some p =>
        rcases p with ⟨x, s'⟩
        simp only [hr] at h
        split at h
        next hk =>
          cases hc : (report x a (budget - charge)).1 with
          | none => simp only [hc] at h; contradiction
          | some p =>
            rcases p with ⟨⟨next, halt⟩, remaining⟩
            have hv := hreport x a (budget - charge) (next, halt) remaining hc
            simp only [hc] at h
            split at h
            next hh =>
              cases h
              exact ⟨by simp only [TieReplay.runAcc, hr, hk, ↓reduceIte, ← hv.1, hh],
                hv.2.trans (Nat.sub_le _ _)⟩
            next hh =>
              have hi := ih s' next (q + 1) (r + 1) remaining out left h
              exact ⟨by simpa only [TieReplay.runAcc, hr, hk, ↓reduceIte, ← hv.1, hh,
                Bool.false_eq_true] using hi.1, hi.2.trans (hv.2.trans (Nat.sub_le _ _))⟩
        next hk =>
          cases h
          exact ⟨by simp only [TieReplay.runAcc, hr, hk, ↓reduceIte], Nat.sub_le _ _⟩
    next _ => contradiction

/-- Both successful and interrupted inner replays are covered. -/
theorem execute_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ) (R L charge : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hcharge : R + L + 8 ≤ charge)
    (hwork : ∀ x a b, (report x a b).2 ≤ b + 1)
    (hspent : ∀ x a b v left, (report x a b).1 = some (v, left) →
      left ≤ b ∧ (report x a b).2 ≤ b - left)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :
    (execute charge read key K report fuel s a q r budget).2 ≤ budget + 1 := by
  induction fuel generalizing s a q r budget with
  | zero => rw [execute]; split <;> dsimp only <;> omega
  | succ fuel ih =>
    have hread := hr s
    rw [execute]
    split
    next hb =>
      cases hv : (read s).1 with
      | none => simp only [hv]; omega
      | some p =>
        rcases p with ⟨x, s'⟩
        have hkey := hk x
        simp only [hv]
        split
        · have hw := hwork x a (budget - charge)
          cases hc : (report x a (budget - charge)).1 with
          | none => dsimp only; omega
          | some p =>
            rcases p with ⟨⟨next, halt⟩, remaining⟩
            have hs := hspent x a (budget - charge) (next, halt) remaining hc
            dsimp only
            split
            · (try dsimp only); omega
            · have hi := ih s' next (q + 1) (r + 1) remaining
              try dsimp only
              omega
        · (try dsimp only); omega
    next _ => (try dsimp only); omega

theorem execute_spent (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → ℕ → Option ((τ × Bool) × ℕ) × ℕ) (R L charge : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hcharge : R + L + 8 ≤ charge)
    (hspent : ∀ x a b v left, (report x a b).1 = some (v, left) →
      left ≤ b ∧ (report x a b).2 ≤ b - left)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) (out : TieReplay.Result σ τ) (left : ℕ)
    (h : (execute charge read key K report fuel s a q r budget).1 = some (out, left)) :
    left ≤ budget ∧
      (execute charge read key K report fuel s a q r budget).2 ≤ budget - left := by
  induction fuel generalizing s a q r budget out left with
  | zero =>
    rw [execute] at h ⊢
    split at h
    next hb =>
      simp only [hb, ↓reduceIte]
      cases h
      try dsimp only
      omega
    next _ => contradiction
  | succ fuel ih =>
    have hread := hr s
    rw [execute] at h ⊢
    split at h
    next hb =>
      simp only [hb, ↓reduceIte] at h ⊢
      cases hv : (read s).1 with
      | none =>
        simp only [hv] at h ⊢
        cases h
        omega
      | some p =>
        rcases p with ⟨x, s'⟩
        have hkey := hk x
        simp only [hv] at h ⊢
        split at h
        next heq =>
          simp only [heq, ↓reduceIte] at h ⊢
          cases hc : (report x a (budget - charge)).1 with
          | none => simp only [hc] at h; contradiction
          | some p =>
            rcases p with ⟨⟨next, halt⟩, remaining⟩
            have hs := hspent x a (budget - charge) (next, halt) remaining hc
            simp only [hc] at h ⊢
            split at h
            next hh =>
              simp only [hh, ↓reduceIte]
              cases h
              omega
            next hh =>
              simp only [hh, Bool.false_eq_true, ↓reduceIte] at h ⊢
              have hi := ih s' next (q + 1) (r + 1) remaining out left h
              omega
        next heq =>
          simp only [heq, ↓reduceIte]
          cases h
          omega
    next _ => contradiction

end LowSpaceSubsetSum.BudgetedOuterReplay

end OAI
