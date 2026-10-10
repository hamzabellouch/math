import OAI.Combinatorics.LowSpaceSubsetSum.Counting.CountedReplay

namespace OAI

/-! # Replay with a budget checked before every iteration

`charge` is a bound for one read, one key, one callback and the loop's
bookkeeping. A failed check returns before evaluating any of these operations.
In the parent join this charge is polynomial in the input scale. The callback
here is the bounded dictionary emitter, not another unbounded replay.
-/

namespace LowSpaceSubsetSum.BudgetedReplay

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def runAcc (charge : ℕ) (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) :
    ℕ → σ → τ → ℕ → ℕ → ℕ → Option (TieReplay.Result σ τ × ℕ)
  | fuel, s, a, q, r, budget =>
    if charge ≤ budget then
      let left := budget - charge
      match fuel with
      | 0 => some (⟨s, a, q, r, false, false⟩, left)
      | fuel + 1 =>
        match read s with
        | none => some (⟨s, a, q + 1, r, true, false⟩, left)
        | some (x, s') =>
          if key x = K then
            let out := report x a
            if out.2 then some (⟨s', out.1, q + 1, r + 1, false, true⟩, left)
            else runAcc charge read key K report fuel s' out.1 (q + 1) (r + 1) left
          else some (⟨s, a, q + 1, r, true, false⟩, left)
    else none

theorem insufficient (charge : ℕ) (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (h : budget < charge) : runAcc charge read key K report fuel s a q r budget = none := by
  rw [runAcc, ite_eq_right (by omega)]

/-- Every completed budgeted execution is exactly the original replay. -/
theorem runAcc_value (charge : ℕ) (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (out : TieReplay.Result σ τ) (left : ℕ)
    (h : runAcc charge read key K report fuel s a q r budget = some (out, left)) :
    out = TieReplay.runAcc read key K report fuel s a q r ∧ left ≤ budget := by
  induction fuel generalizing s a q r budget out left with
  | zero =>
    rw [runAcc] at h
    split at h
    · cases h
      exact ⟨rfl, Nat.sub_le _ _⟩
    · contradiction
  | succ fuel ih =>
    rw [runAcc] at h
    split at h
    next hbudget =>
      cases hr : read s with
      | none =>
        simp only [hr] at h
        cases h
        exact ⟨by simp only [TieReplay.runAcc, hr], Nat.sub_le _ _⟩
      | some p =>
        rcases p with ⟨x, s'⟩
        simp only [hr] at h
        split at h
        next hk =>
          split at h
          next hp =>
            cases h
            exact ⟨by simp only [TieReplay.runAcc, hr, hk, ↓reduceIte, hp], Nat.sub_le _ _⟩
          next hp =>
            obtain ⟨hv, hl⟩ := ih s' (report x a).1 (q + 1) (r + 1) _ out left h
            exact ⟨by simpa only [TieReplay.runAcc, hr, hk, ↓reduceIte, hp, Bool.false_eq_true] using hv,
              hl.trans (Nat.sub_le _ _)⟩
        next hk =>
          cases h
          exact ⟨by simp only [TieReplay.runAcc, hr, hk, ↓reduceIte], Nat.sub_le _ _⟩
    next hbudget => contradiction

private theorem queries_mono (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (fuel : ℕ) (s : σ) (a : τ) (q r : ℕ) :
    q ≤ (TieReplay.runAcc read key K report fuel s a q r).queries := by
  induction fuel generalizing s a q r with
  | zero => exact le_rfl
  | succ fuel ih =>
    cases hr : read s with
    | none => simp only [TieReplay.runAcc, hr]; omega
    | some p =>
      rcases p with ⟨x, s'⟩
      simp only [TieReplay.runAcc, hr]
      split
      · split
        · ((try dsimp only); omega)
        · exact (Nat.le_succ q).trans (ih _ _ _ _)
      · ((try dsimp only); omega)

/-- Enough prepaid iterations guarantee completion. The number of iterations
is bounded by the original replay's query counter, not its unused fuel. -/
theorem runAcc_complete (charge : ℕ) (read : σ → Option (α × σ)) (key : α → ℤ) (K : ℤ)
    (report : α → τ → τ × Bool) (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (hbudget : charge * ((TieReplay.runAcc read key K report fuel s a q r).queries - q + 1)
      ≤ budget) :
    ∃ left, runAcc charge read key K report fuel s a q r budget =
      some (TieReplay.runAcc read key K report fuel s a q r, left) := by
  induction fuel generalizing s a q r budget with
  | zero =>
    simp only [TieReplay.runAcc, Nat.sub_self, Nat.zero_add, Nat.mul_one] at hbudget
    exact ⟨budget - charge, by rw [runAcc, ite_eq_left hbudget]; rfl⟩
  | succ fuel ih =>
    have hcharge : charge ≤ budget := by
      have hm := Nat.mul_le_mul_left charge
        (show 1 ≤ (TieReplay.runAcc read key K report (fuel + 1) s a q r).queries - q + 1 by omega)
      simpa only [Nat.mul_one] using hm.trans hbudget
    rw [runAcc, ite_eq_left hcharge]
    cases hr : read s with
    | none => exact ⟨budget - charge, by simp only [TieReplay.runAcc, hr]⟩
    | some p =>
      rcases p with ⟨x, s'⟩
      by_cases hk : key x = K
      · simp only [hk, ↓reduceIte]
        by_cases hp : (report x a).2 = true
        · exact ⟨budget - charge, by simp only [hp, ↓reduceIte, TieReplay.runAcc, hr, hk]⟩
        · simp only [hp, Bool.false_eq_true, ↓reduceIte]
          have hmono : q + 1 ≤ (TieReplay.runAcc read key K report fuel s' (report x a).1
              (q + 1) (r + 1)).queries :=
            queries_mono read key K report fuel s' (report x a).1 (q + 1) (r + 1)
          have hb : charge * ((TieReplay.runAcc read key K report fuel s' (report x a).1
              (q + 1) (r + 1)).queries - (q + 1) + 1) ≤ budget - charge := by
            simp only [TieReplay.runAcc, hr, hk, ↓reduceIte, hp, Bool.false_eq_true] at hbudget
            have he : (TieReplay.runAcc read key K report fuel s' (report x a).1
                (q + 1) (r + 1)).queries - q =
                (TieReplay.runAcc read key K report fuel s' (report x a).1
                (q + 1) (r + 1)).queries - (q + 1) + 1 := by omega
            rw [he, Nat.mul_add, Nat.mul_one] at hbudget
            omega
          simpa only [TieReplay.runAcc, hr, hk, ↓reduceIte, hp, Bool.false_eq_true] using
            ih s' (report x a).1 (q + 1) (r + 1) (budget - charge) hb
      · exact ⟨budget - charge, by simp only [hk, ↓reduceIte, TieReplay.runAcc, hr]⟩

/-- The prepaid budget covers the counted primitive work of every completed
execution, including all reads and the callback's actual work. -/
theorem runAcc_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (R L C charge : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 ≤ C) (hcharge : R + L + C + 8 ≤ charge)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) (out : TieReplay.Result σ τ) (left : ℕ)
    (h : runAcc charge (fun s => (read s).1) (fun x => (key x).1) K
      (fun x a => (report x a).1) fuel s a q r budget = some (out, left)) :
    (CountedReplay.runAcc read key K report fuel s a q r).2 ≤ budget - left := by
  induction fuel generalizing s a q r budget out left with
  | zero =>
    rw [runAcc] at h
    split at h
    · cases h
      simp only [CountedReplay.runAcc]
      omega
    · contradiction
  | succ fuel ih =>
    rw [runAcc] at h
    split at h
    next hbudget =>
      have hread := hr s
      cases hv : (read s).1 with
      | none =>
        simp only [hv] at h
        cases h
        simp only [CountedReplay.runAcc, hv]
        omega
      | some p =>
        rcases p with ⟨x, s'⟩
        have hkey := hk x
        have hcallback := hc x a
        simp only [hv] at h
        split at h
        next heq =>
          split at h
          next hhalt =>
            cases h
            simp only [CountedReplay.runAcc, hv, heq, ↓reduceIte, hhalt]
            omega
          next hhalt =>
            have hi := ih s' (report x a).1.1 (q + 1) (r + 1) (budget - charge) out left h
            have hl := (runAcc_value charge (fun s => (read s).1) (fun x => (key x).1) K
              (fun x a => (report x a).1) fuel s' (report x a).1.1 (q + 1) (r + 1)
              (budget - charge) out left h).2
            simp only [CountedReplay.runAcc, hv, heq, ↓reduceIte, hhalt,
              Bool.false_eq_true]
            omega
        next heq =>
          cases h
          simp only [CountedReplay.runAcc, hv, heq, ↓reduceIte]
          omega
    next hbudget => contradiction

/-- The executing version retains a work counter even when the budget test
aborts. The guard precedes every counted read/key/report call. -/
def execute (charge : ℕ) (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) :
    ℕ → σ → τ → ℕ → ℕ → ℕ → (Option (TieReplay.Result σ τ × ℕ) × ℕ)
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
            let out := report x a
            if out.1.2 then
              (some (⟨s', out.1.1, q + 1, r + 1, false, true⟩, left),
                fetched.2 + found.2 + out.2 + 8)
            else
              let rest := execute charge read key K report fuel s' out.1.1
                (q + 1) (r + 1) left
              (rest.1, fetched.2 + found.2 + out.2 + 8 + rest.2)
          else (some (⟨s, a, q + 1, r, true, false⟩, left), fetched.2 + found.2 + 6)
    else (none, 1)

theorem execute_value (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :
    (execute charge read key K report fuel s a q r budget).1 =
      runAcc charge (fun s => (read s).1) (fun x => (key x).1) K
        (fun x a => (report x a).1) fuel s a q r budget := by
  induction fuel generalizing s a q r budget with
  | zero => simp only [execute, runAcc]; split <;> rfl
  | succ fuel ih =>
    rw [execute, runAcc]
    split
    · dsimp only
      cases hv : (read s).1 with
      | none => rfl
      | some p =>
        rcases p with ⟨x, s'⟩
        dsimp only
        split
        · split
          · rfl
          · exact ih _ _ _ _ _
        · rfl
    · rfl

/-- This includes exhausted-budget executions. One final failed comparison
can add one operation after the prepaid budget has been consumed. -/
theorem execute_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (R L C charge : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 ≤ C) (hcharge : R + L + C + 8 ≤ charge)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) :
    (execute charge read key K report fuel s a q r budget).2 ≤ budget + 1 := by
  induction fuel generalizing s a q r budget with
  | zero => simp only [execute]; split <;> dsimp only <;> omega
  | succ fuel ih =>
    have hread := hr s
    rw [execute]
    split
    next hbudget =>
      dsimp only
      cases hv : (read s).1 with
      | none => ((try dsimp only); omega)
      | some p =>
        rcases p with ⟨x, s'⟩
        have hkey := hk x
        have hcallback := hc x a
        dsimp only
        split
        · split
          · ((try dsimp only); omega)
          · have hi := ih s' (report x a).1.1 (q + 1) (r + 1) (budget - charge)
            try dsimp only
            omega
        · ((try dsimp only); omega)
    next hbudget => ((try dsimp only); omega)

/-- A completed execution performs precisely the reference operations.
This equality permits nested callers to retain the unspent budget. -/
theorem execute_work_eq (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (out : TieReplay.Result σ τ) (left : ℕ)
    (h : (execute charge read key K report fuel s a q r budget).1 = some (out, left)) :
    (execute charge read key K report fuel s a q r budget).2 =
      (CountedReplay.runAcc read key K report fuel s a q r).2 := by
  induction fuel generalizing s a q r budget out left with
  | zero =>
    rw [execute] at h ⊢
    split at h
    next hb => simp only [hb, ↓reduceIte, CountedReplay.runAcc]
    next _ => contradiction
  | succ fuel ih =>
    rw [execute] at h ⊢
    split at h
    next hb =>
      simp only [hb, ↓reduceIte] at h ⊢
      rw [CountedReplay.runAcc]
      cases hv : (read s).1 with
      | none => rfl
      | some p =>
        rcases p with ⟨x, s'⟩
        simp only [hv] at h ⊢
        by_cases he : (key x).1 = K
        · simp only [he, ↓reduceIte] at h ⊢
          by_cases hh : (report x a).1.2 = true
          · simp only [hh, ↓reduceIte]
          · simp only [hh, Bool.false_eq_true, ↓reduceIte] at h ⊢
            rw [ih s' (report x a).1.1 (q + 1) (r + 1) (budget - charge) out left h]
        · simp only [he, ↓reduceIte]
    next _ => contradiction

theorem execute_spent (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (R L C charge : ℕ)
    (hr : ∀ s, (read s).2 ≤ R) (hk : ∀ x, (key x).2 ≤ L)
    (hc : ∀ x a, (report x a).2 ≤ C) (hcharge : R + L + C + 8 ≤ charge)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ) (out : TieReplay.Result σ τ) (left : ℕ)
    (h : (execute charge read key K report fuel s a q r budget).1 = some (out, left)) :
    (execute charge read key K report fuel s a q r budget).2 ≤ budget - left := by
  rw [execute_work_eq charge read key K report fuel s a q r budget out left h]
  apply runAcc_work read key K report R L C charge hr hk hc hcharge fuel s a q r budget out left
  rw [← execute_value]
  exact h

/-- The discarded allowance is bounded by the performed queries plus one
terminal check, which supports completion proofs for sequential stages. -/
theorem runAcc_remaining (charge : ℕ) (read : σ → Option (α × σ))
    (key : α → ℤ) (K : ℤ) (report : α → τ → τ × Bool)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (out : TieReplay.Result σ τ) (left : ℕ)
    (h : runAcc charge read key K report fuel s a q r budget = some (out, left)) :
    budget ≤ left + charge * (out.queries - q + 1) := by
  induction fuel generalizing s a q r budget out left with
  | zero =>
    rw [runAcc] at h
    split at h
    next hb =>
      cases h
      simp only [Nat.sub_self, Nat.zero_add, Nat.mul_one]
      omega
    next _ => contradiction
  | succ fuel ih =>
    rw [runAcc] at h
    split at h
    next hb =>
      cases hv : read s with
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
          split at h
          next hh =>
            cases h
            have hq : q + 1 - q + 1 = 2 := by omega
            change budget ≤ budget - charge + charge * (q + 1 - q + 1)
            rw [hq]
            omega
          next hh =>
            have hi := ih s' (report x a).1 (q + 1) (r + 1) (budget - charge) out left h
            have he := (runAcc_value charge read key K report fuel s' (report x a).1
              (q + 1) (r + 1) (budget - charge) out left h).1
            have hm := queries_mono read key K report fuel s' (report x a).1 (q + 1) (r + 1)
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

theorem execute_remaining (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (out : TieReplay.Result σ τ) (left : ℕ)
    (h : (execute charge read key K report fuel s a q r budget).1 = some (out, left)) :
    budget ≤ left + charge * (out.queries - q + 1) := by
  apply runAcc_remaining charge (fun s => (read s).1) (fun x => (key x).1) K
    (fun x a => (report x a).1) fuel s a q r budget out left
  rw [← execute_value]
  exact h

/-- The counted reference value of a completed execution. -/
theorem execute_result (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (out : TieReplay.Result σ τ) (left : ℕ)
    (h : (execute charge read key K report fuel s a q r budget).1 = some (out, left)) :
    out = (CountedReplay.runAcc read key K report fuel s a q r).1 ∧ left ≤ budget := by
  rw [execute_value] at h
  have hv := runAcc_value charge (fun s => (read s).1) (fun x => (key x).1) K
    (fun x a => (report x a).1) fuel s a q r budget out left h
  exact ⟨hv.1.trans (CountedReplay.runAcc_value read key K report fuel s a q r).symm, hv.2⟩

theorem execute_complete (charge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (fuel : ℕ) (s : σ) (a : τ) (q r budget : ℕ)
    (hbudget : charge * ((CountedReplay.runAcc read key K report fuel s a q r).1.queries - q + 1)
      ≤ budget) :
    ∃ left, (execute charge read key K report fuel s a q r budget).1 =
      some ((CountedReplay.runAcc read key K report fuel s a q r).1, left) := by
  rw [CountedReplay.runAcc_value] at hbudget ⊢
  rw [execute_value]
  exact runAcc_complete charge (fun s => (read s).1) (fun x => (key x).1) K
    (fun x a => (report x a).1) fuel s a q r budget hbudget

end LowSpaceSubsetSum.BudgetedReplay

end OAI
