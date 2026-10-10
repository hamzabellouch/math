import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedFill

namespace OAI

/-! # Prepaid construction of a tie buffer

The budget guard precedes the reader, key evaluator and record copy. It can
therefore interrupt a long tie before materializing the entire requested
buffer. The reference fill appears only in correctness and completion proofs.
-/

namespace LowSpaceSubsetSum.BudgetedFill

universe u v
variable {α : Type u} {σ : Type v}

def execute (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ) :
    ℕ → σ → Array α → ℕ → ℕ → Option (TieBuffer.Result α σ × ℕ) × ℕ
  | fuel, s, buf, q, budget =>
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => (some (⟨buf, s, q⟩, left), 1)
      | fuel + 1 =>
        let fetched := read s
        match fetched.1 with
        | none => (some (⟨buf, s, q + 1⟩, left), fetched.2 + 5)
        | some (x, s') =>
          let found := key x
          if found.1 = K then
            let rest := execute charge read key cells K fuel s' (buf.push x) (q + 1) left
            (rest.1, fetched.2 + found.2 + cells x + 8 + rest.2)
          else (some (⟨buf, s, q + 1⟩, left), fetched.2 + found.2 + 6)
    else (none, 1)

theorem insufficient (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget : ℕ) (h : budget < charge) :
    execute charge read key cells K fuel s buf q budget = (none, 1) := by
  rw [execute, ite_eq_right (by omega)]

theorem execute_value (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget : ℕ)
    (out : TieBuffer.Result α σ) (left : ℕ)
    (h : (execute charge read key cells K fuel s buf q budget).1 = some (out, left)) :
    out = (CountedFill.fillAcc read key cells K fuel s buf q).1 ∧ left ≤ budget := by
  induction fuel generalizing s buf q budget out left with
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
      dsimp only at h
      cases hv : (read s).1 with
      | none =>
        simp only [hv] at h
        cases h
        exact ⟨by simp only [CountedFill.fillAcc, hv], Nat.sub_le _ _⟩
      | some p =>
        rcases p with ⟨x, s'⟩
        simp only [hv] at h
        split at h
        next hk =>
          obtain ⟨he, hl⟩ := ih s' (buf.push x) (q + 1) _ out left h
          exact ⟨by simpa only [CountedFill.fillAcc, hv, hk, ↓reduceIte] using he,
            hl.trans (Nat.sub_le _ _)⟩
        next hk =>
          cases h
          exact ⟨by simp only [CountedFill.fillAcc, hv, hk, ↓reduceIte], Nat.sub_le _ _⟩
    next hb => contradiction

private theorem queries_mono (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q : ℕ) :
    q ≤ (CountedFill.fillAcc read key cells K fuel s buf q).1.queries := by
  induction fuel generalizing s buf q with
  | zero => exact le_rfl
  | succ fuel ih =>
    rw [CountedFill.fillAcc]
    cases hv : (read s).1 with
    | none => simp only; omega
    | some p =>
      rcases p with ⟨x, s'⟩
      dsimp only
      split
      · exact (Nat.le_succ q).trans (ih _ _ _)
      · simp only; omega

theorem execute_complete (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget : ℕ)
    (hbudget : charge * ((CountedFill.fillAcc read key cells K fuel s buf q).1.queries - q + 1)
      ≤ budget) :
    ∃ left, (execute charge read key cells K fuel s buf q budget).1 =
      some ((CountedFill.fillAcc read key cells K fuel s buf q).1, left) := by
  induction fuel generalizing s buf q budget with
  | zero =>
    change charge * (q - q + 1) ≤ budget at hbudget
    simp only [Nat.sub_self, Nat.zero_add, Nat.mul_one] at hbudget
    exact ⟨budget - charge, by rw [execute, ite_eq_left hbudget]; rfl⟩
  | succ fuel ih =>
    have hc : charge ≤ budget := by
      have hm := Nat.mul_le_mul_left charge
        (show 1 ≤ (CountedFill.fillAcc read key cells K (fuel + 1) s buf q).1.queries - q + 1
          by omega)
      simpa only [Nat.mul_one] using hm.trans hbudget
    rw [execute, ite_eq_left hc]
    dsimp only
    cases hv : (read s).1 with
    | none => exact ⟨budget - charge, by simp only [CountedFill.fillAcc, hv]⟩
    | some p =>
      rcases p with ⟨x, s'⟩
      dsimp only
      by_cases hk : (key x).1 = K
      · simp only [hk, ↓reduceIte]
        have hm := queries_mono read key cells K fuel s' (buf.push x) (q + 1)
        have hb : charge *
            ((CountedFill.fillAcc read key cells K fuel s' (buf.push x) (q + 1)).1.queries -
              (q + 1) + 1) ≤ budget - charge := by
          simp only [CountedFill.fillAcc, hv, hk, ↓reduceIte] at hbudget
          have he :
              (CountedFill.fillAcc read key cells K fuel s' (buf.push x) (q + 1)).1.queries - q =
              (CountedFill.fillAcc read key cells K fuel s' (buf.push x) (q + 1)).1.queries -
                (q + 1) + 1 := by omega
          rw [he, Nat.mul_add, Nat.mul_one] at hbudget
          omega
        simpa only [CountedFill.fillAcc, hv, hk, ↓reduceIte] using
          ih s' (buf.push x) (q + 1) (budget - charge) hb
      · exact ⟨budget - charge, by simp only [hk, ↓reduceIte, CountedFill.fillAcc, hv]⟩

theorem execute_work (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ) (R L S charge : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hs : ∀ x, cells x ≤ S) (hcharge : R + L + S + 8 ≤ charge)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget : ℕ) :
    (execute charge read key cells K fuel s buf q budget).2 ≤ budget + 1 := by
  induction fuel generalizing s buf q budget with
  | zero => simp only [execute]; split <;> dsimp only <;> omega
  | succ fuel ih =>
    have hread := hr s
    rw [execute]
    split
    next hb =>
      dsimp only
      cases hv : (read s).1 with
      | none => ((try dsimp only); omega)
      | some p =>
        rcases p with ⟨x, s'⟩
        have hkey := hk x
        have hcell := hs x
        dsimp only
        split
        · have hi := ih s' (buf.push x) (q + 1) (budget - charge)
          try dsimp only
          omega
        · ((try dsimp only); omega)
    next hb => ((try dsimp only); omega)

/-- A successful fill charges its work against the budget it actually spent,
so the remaining allowance can be passed to the next join stage. -/
theorem execute_spent (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ) (R L S charge : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hs : ∀ x, cells x ≤ S) (hcharge : R + L + S + 8 ≤ charge)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget : ℕ)
    (out : TieBuffer.Result α σ) (left : ℕ)
    (h : (execute charge read key cells K fuel s buf q budget).1 = some (out, left)) :
    (execute charge read key cells K fuel s buf q budget).2 ≤ budget - left := by
  induction fuel generalizing s buf q budget out left with
  | zero =>
    rw [execute] at h ⊢
    split at h
    next hb =>
      simp only [hb, ↓reduceIte] at h ⊢
      cases h
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
        have hcell := hs x
        simp only [hv] at h ⊢
        by_cases he : (key x).1 = K
        · simp only [he, ↓reduceIte] at h ⊢
          have hi := ih s' (buf.push x) (q + 1) (budget - charge) out left h
          have hl := (execute_value charge read key cells K fuel s' (buf.push x)
            (q + 1) (budget - charge) out left h).2
          omega
        · simp only [he, ↓reduceIte] at h ⊢
          cases h
          omega
    next _ => contradiction

/-- The discarded fill allowance is bounded by its performed queries. -/
theorem execute_remaining (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (cells : α → ℕ) (K : ℤ)
    (fuel : ℕ) (s : σ) (buf : Array α) (q budget : ℕ)
    (out : TieBuffer.Result α σ) (left : ℕ)
    (h : (execute charge read key cells K fuel s buf q budget).1 = some (out, left)) :
    budget ≤ left + charge * (out.queries - q + 1) := by
  induction fuel generalizing s buf q budget out left with
  | zero =>
    rw [execute] at h
    split at h
    next hb =>
      cases h
      simp only [Nat.sub_self, Nat.zero_add, Nat.mul_one]
      omega
    next _ => contradiction
  | succ fuel ih =>
    rw [execute] at h
    split at h
    next hb =>
      cases hv : (read s).1 with
      | none =>
        simp only [hv] at h
        cases h
        have hq : q + 1 - q + 1 = 2 := by omega
        change budget ≤ budget - charge + charge * (q + 1 - q + 1)
        rw [hq]
        omega
      | some p =>
        rcases p with ⟨x, s'⟩
        simp only [hv] at h
        split at h
        next hk =>
          have hi := ih s' (buf.push x) (q + 1) (budget - charge) out left h
          have he := (execute_value charge read key cells K fuel s' (buf.push x)
            (q + 1) (budget - charge) out left h).1
          have hm := queries_mono read key cells K fuel s' (buf.push x) (q + 1)
          rw [← he] at hm
          have hq : out.queries - q + 1 = (out.queries - (q + 1) + 1) + 1 := by omega
          rw [hq, Nat.mul_add, Nat.mul_one]
          omega
        next hk =>
          cases h
          have hq : q + 1 - q + 1 = 2 := by omega
          change budget ≤ budget - charge + charge * (q + 1 - q + 1)
          rw [hq]
          omega
    next _ => contradiction

end LowSpaceSubsetSum.BudgetedFill

end OAI
