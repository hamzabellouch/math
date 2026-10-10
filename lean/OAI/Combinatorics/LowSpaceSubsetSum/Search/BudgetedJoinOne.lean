import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedReplay
import OAI.Combinatorics.LowSpaceSubsetSum.Search.BudgetedReplayLoops
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.CountedJoinOne

namespace OAI

/-! # Prepaid buffered replay and suffix restoration

The fixed overhead and snapshot allowance are reserved before their operations.
The suffix receives only the allowance left by the completed buffer replay.
No branch tests the cost of an operation after executing it.
-/

namespace LowSpaceSubsetSum.BudgetedJoinOne

universe u v w
variable {α : Type u} {σ : Type v} {τ : Type w}

def execute (charge copyCharge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array α) (saved : σ) (long : Bool)
    (fuel : ℕ) (a : τ) (budget : ℕ) : Option (TieReplay.Result σ τ × ℕ) × ℕ :=
  if 6 ≤ budget then
    let first := BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
      key K report buffer.size 0 a 0 0 (budget - 6)
    match first.1 with
    | none => (none, first.2 + 6)
    | some (out, left) =>
      if out.halted then
        (some (⟨saved, out.state, out.queries, out.reports, false, true⟩, left), first.2 + 6)
      else if long then
        if copyCharge ≤ left then
          let copied := clone saved
          let rest := BudgetedReplay.execute charge read key K report fuel copied.1
            out.state 0 0 (left - copyCharge)
          (rest.1.map (fun (tail, remaining) =>
            (⟨tail.cursor, tail.state, out.queries + tail.queries,
              out.reports + tail.reports, tail.complete, tail.halted⟩, remaining)),
            first.2 + copied.2 + rest.2 + 6)
        else (none, first.2 + 7)
      else
        (some (⟨saved, out.state, out.queries, out.reports, true, false⟩, left), first.2 + 6)
  else (none, 1)

theorem execute_value (charge copyCharge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array α) (saved : σ) (long : Bool)
    (fuel : ℕ) (a : τ) (budget : ℕ) (out : TieReplay.Result σ τ) (remaining : ℕ)
    (h : (execute charge copyCharge read key K report clone buffer saved long fuel a budget).1 =
      some (out, remaining)) :
    out = (CountedJoinOne.run read key K report clone buffer saved long fuel a).1 ∧
      remaining ≤ budget := by
  let first := BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6)
  have hfirst : BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6) = first := rfl
  rw [execute] at h
  split at h
  next hb =>
    simp only [hfirst] at h
    cases hf : first.1 with
    | none => simp only [hf] at h; contradiction
    | some p =>
      rcases p with ⟨front, left⟩
      have hv := BudgetedReplay.execute_result charge (fun i => (BufferReplay.read buffer i, 4))
        key K report buffer.size 0 a 0 0 (budget - 6) front left hf
      obtain ⟨hv, hvleft⟩ := hv
      change front = (CountedReplay.run _ key K report buffer.size 0 a).1 at hv
      simp only [hf] at h
      rw [CountedJoinOne.run, ← hv]
      split at h
      next hh =>
        cases h
        exact ⟨by simp only [hh, ↓reduceIte], hvleft.trans (Nat.sub_le _ _)⟩
      next hh =>
        simp only [hh, Bool.false_eq_true, ↓reduceIte]
        split at h
        next hl =>
          simp only [hl, ↓reduceIte]
          split at h
          next hc =>
            dsimp only at h
            obtain ⟨pair, hp, he⟩ := Option.map_eq_some_iff.mp h
            rcases pair with ⟨tail, rest⟩
            have ht := BudgetedReplay.execute_result charge read key K report fuel (clone saved).1
              front.state 0 0 (left - copyCharge) tail rest hp
            cases he
            exact ⟨by rw [ht.1]; rfl,
              ht.2.trans ((Nat.sub_le _ _).trans (hvleft.trans (Nat.sub_le _ _)))⟩
          next _ => contradiction
        next hl =>
          cases h
          exact ⟨by simp only [hl, Bool.false_eq_true, ↓reduceIte],
            hvleft.trans (Nat.sub_le _ _)⟩
  next _ => contradiction

/-- Every outcome, including either failed guard, stays within the allowance
plus its final failed comparison. -/
theorem execute_work (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (clone : σ → σ × ℕ)
    (R L C charge copyCharge : ℕ) (hr : ∀ s, (read s).2 ≤ R)
    (hk : ∀ x, (key x).2 ≤ L) (hc : ∀ x a, (report x a).2 ≤ C)
    (hcharge : max R 4 + L + C + 8 ≤ charge) (hcopy : ∀ s, (clone s).2 ≤ copyCharge)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) (budget : ℕ) :
    (execute charge copyCharge read key K report clone buffer saved long fuel a budget).2 ≤
      budget + 1 := by
  have hcb : 4 + L + C + 8 ≤ charge := by omega
  have hcr : R + L + C + 8 ≤ charge := by omega
  let first := BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6)
  have hfirst : BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6) = first := rfl
  have hw := BudgetedReplay.execute_work (fun i => (BufferReplay.read buffer i, 4)) key K report
    4 L C charge (fun _ => le_rfl) hk hc hcb buffer.size 0 a 0 0 (budget - 6)
  change first.2 ≤ budget - 6 + 1 at hw
  rw [execute]
  split
  next hb =>
    simp only [hfirst]
    cases hf : first.1 with
    | none => (try dsimp only); omega
    | some p =>
      rcases p with ⟨front, left⟩
      have hv := BudgetedReplay.execute_result charge (fun i => (BufferReplay.read buffer i, 4))
        key K report buffer.size 0 a 0 0 (budget - 6) front left hf
      have hs := BudgetedReplay.execute_spent (fun i => (BufferReplay.read buffer i, 4)) key K report
        4 L C charge (fun _ => le_rfl) hk hc hcb buffer.size 0 a 0 0 (budget - 6) front left hf
      change first.2 ≤ budget - 6 - left at hs
      dsimp only
      split
      · (try dsimp only); omega
      · split
        · split
          · have ht := BudgetedReplay.execute_work read key K report R L C charge hr hk hc hcr
              fuel (clone saved).1 front.state 0 0 (left - copyCharge)
            have hcp := hcopy saved
            try dsimp only
            omega
          · (try dsimp only); omega
        · (try dsimp only); omega
  next _ => (try dsimp only); omega

/-- Successful nested calls leave the claimed allowance unspent. -/
theorem execute_spent (read : σ → Option (α × σ) × ℕ) (key : α → ℤ × ℕ) (K : ℤ)
    (report : α → τ → (τ × Bool) × ℕ) (clone : σ → σ × ℕ)
    (R L C charge copyCharge : ℕ) (hr : ∀ s, (read s).2 ≤ R)
    (hk : ∀ x, (key x).2 ≤ L) (hc : ∀ x a, (report x a).2 ≤ C)
    (hcharge : max R 4 + L + C + 8 ≤ charge) (hcopy : ∀ s, (clone s).2 ≤ copyCharge)
    (buffer : Array α) (saved : σ) (long : Bool) (fuel : ℕ) (a : τ) (budget : ℕ)
    (out : TieReplay.Result σ τ) (remaining : ℕ)
    (h : (execute charge copyCharge read key K report clone buffer saved long fuel a budget).1 =
      some (out, remaining)) :
    (execute charge copyCharge read key K report clone buffer saved long fuel a budget).2 ≤
      budget - remaining := by
  have hcb : 4 + L + C + 8 ≤ charge := by omega
  have hcr : R + L + C + 8 ≤ charge := by omega
  let first := BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6)
  have hfirst : BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6) = first := rfl
  rw [execute] at h ⊢
  split at h
  next hb =>
    simp only [hb, ↓reduceIte, hfirst] at h ⊢
    cases hf : first.1 with
    | none => simp only [hf] at h; contradiction
    | some p =>
      rcases p with ⟨front, left⟩
      have hv := BudgetedReplay.execute_result charge (fun i => (BufferReplay.read buffer i, 4))
        key K report buffer.size 0 a 0 0 (budget - 6) front left hf
      have hs := BudgetedReplay.execute_spent (fun i => (BufferReplay.read buffer i, 4)) key K report
        4 L C charge (fun _ => le_rfl) hk hc hcb buffer.size 0 a 0 0 (budget - 6) front left hf
      change first.2 ≤ budget - 6 - left at hs
      simp only [hf] at h ⊢
      split at h
      next hh =>
        simp only [hh, ↓reduceIte]
        cases h
        try dsimp only
        omega
      next hh =>
        simp only [hh, Bool.false_eq_true, ↓reduceIte] at h ⊢
        split at h
        next hl =>
          simp only [hl, ↓reduceIte] at h ⊢
          split at h
          next hp =>
            simp only [hp, ↓reduceIte] at h ⊢
            obtain ⟨pair, ht, he⟩ := Option.map_eq_some_iff.mp h
            rcases pair with ⟨tail, rest⟩
            have hrst := BudgetedReplay.execute_spent read key K report R L C charge hr hk hc hcr
              fuel (clone saved).1 front.state 0 0 (left - copyCharge) tail rest ht
            have hrleft := (BudgetedReplay.execute_result charge read key K report fuel
              (clone saved).1 front.state 0 0 (left - copyCharge) tail rest ht).2
            have hcp := hcopy saved
            cases he
            try dsimp only
            omega
          next _ => contradiction
        next hl =>
          simp only [hl, Bool.false_eq_true, ↓reduceIte]
          cases h
          try dsimp only
          omega
  next _ => contradiction

/-- Completion is governed by performed queries and actual restores, not
by multiplying the two advertised stream fuel bounds. -/
theorem execute_complete (charge copyCharge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array α) (saved : σ) (long : Bool)
    (fuel : ℕ) (a : τ) (budget : ℕ)
    (hbudget : charge * ((CountedJoinOne.run read key K report clone buffer saved long fuel a).1.queries + 2) +
      (if long then copyCharge else 0) + 6 ≤ budget) :
    ∃ remaining, (execute charge copyCharge read key K report clone buffer saved long fuel a budget).1 =
      some ((CountedJoinOne.run read key K report clone buffer saved long fuel a).1, remaining) := by
  let front := (CountedReplay.run (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a).1
  have hfdef : (CountedReplay.run (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a).1 = front := rfl
  have hq : front.queries ≤ (CountedJoinOne.run read key K report clone buffer saved long fuel a).1.queries := by
    simp only [CountedJoinOne.run, hfdef]
    split
    · exact le_rfl
    · split
      · (try dsimp only); omega
      · exact le_rfl
  have hb : 6 ≤ budget := by omega
  have hfallow : charge * (front.queries + 1) ≤ budget - 6 := by
    have hm := Nat.mul_le_mul_left charge (show front.queries + 1 ≤
      (CountedJoinOne.run read key K report clone buffer saved long fuel a).1.queries + 2 by omega)
    omega
  obtain ⟨left, hfirst⟩ := BudgetedReplay.execute_complete charge
    (fun i => (BufferReplay.read buffer i, 4)) key K report buffer.size 0 a 0 0 (budget - 6)
    (by change charge * (front.queries - 0 + 1) ≤ budget - 6
        simpa only [Nat.sub_zero] using hfallow)
  change (BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4)) key K report
    buffer.size 0 a 0 0 (budget - 6)).1 = some (front, left) at hfirst
  have hremaining := BudgetedReplay.execute_remaining charge
    (fun i => (BufferReplay.read buffer i, 4)) key K report buffer.size 0 a 0 0 (budget - 6)
    front left hfirst
  simp only [Nat.sub_zero] at hremaining
  rw [execute, ite_eq_left hb]
  simp only [hfirst]
  by_cases hh : front.halted = true
  · refine ⟨left, ?_⟩
    simp only [hh, ↓reduceIte, CountedJoinOne.run, hfdef]
  · simp only [hh, Bool.false_eq_true, ↓reduceIte]
    by_cases hl : long = true
    · simp only [hl, ↓reduceIte]
      have hm : charge * ((CountedReplay.run read key K report fuel (clone saved).1 front.state).1.queries + 1) +
          copyCharge ≤ left := by
        simp only [CountedJoinOne.run, hfdef, hh, Bool.false_eq_true, hl, ↓reduceIte] at hbudget
        simp only [Nat.mul_add, Nat.mul_one] at hbudget hremaining ⊢
        omega
      have hcopy : copyCharge ≤ left := by omega
      rw [ite_eq_left hcopy]
      obtain ⟨remaining, hrest⟩ := BudgetedReplay.execute_complete charge read key K report
        fuel (clone saved).1 front.state 0 0 (left - copyCharge)
        (by simpa only [CountedReplay.run, Nat.sub_zero] using (show
          charge * ((CountedReplay.run read key K report fuel (clone saved).1 front.state).1.queries + 1) ≤
            left - copyCharge by omega))
      refine ⟨remaining, ?_⟩
      simp only [hrest, Option.map_some, CountedJoinOne.run, hfdef, hh, Bool.false_eq_true,
        ↓reduceIte]
      rfl
    · refine ⟨left, ?_⟩
      simp only [hl, Bool.false_eq_true, ↓reduceIte, CountedJoinOne.run, hfdef, hh]

/-- At most one charge per query, two terminal charges, and one snapshot
allowance are discarded by a completed inner replay. -/
theorem execute_remaining (charge copyCharge : ℕ) (read : σ → Option (α × σ) × ℕ)
    (key : α → ℤ × ℕ) (K : ℤ) (report : α → τ → (τ × Bool) × ℕ)
    (clone : σ → σ × ℕ) (buffer : Array α) (saved : σ) (long : Bool)
    (fuel : ℕ) (a : τ) (budget : ℕ) (out : TieReplay.Result σ τ) (remaining : ℕ)
    (h : (execute charge copyCharge read key K report clone buffer saved long fuel a budget).1 =
      some (out, remaining)) :
    budget ≤ remaining + charge * (out.queries + 2) + (if long then copyCharge else 0) + 6 := by
  let first := BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6)
  have hfirst : BudgetedReplay.execute charge (fun i => (BufferReplay.read buffer i, 4))
    key K report buffer.size 0 a 0 0 (budget - 6) = first := rfl
  rw [execute] at h
  split at h
  next hb =>
    simp only [hfirst] at h
    cases hf : first.1 with
    | none => simp only [hf] at h; contradiction
    | some p =>
      rcases p with ⟨front, left⟩
      have hs := BudgetedReplay.execute_remaining charge (fun i => (BufferReplay.read buffer i, 4))
        key K report buffer.size 0 a 0 0 (budget - 6) front left hf
      simp only [Nat.sub_zero, Nat.mul_add, Nat.mul_one] at hs
      simp only [hf] at h
      split at h
      next hh =>
        cases h
        simp only [Nat.mul_add]
        omega
      next hh =>
        split at h
        next hl =>
          split at h
          next hp =>
            obtain ⟨pair, ht, he⟩ := Option.map_eq_some_iff.mp h
            rcases pair with ⟨tail, rest⟩
            have hrst := BudgetedReplay.execute_remaining charge read key K report fuel
              (clone saved).1 front.state 0 0 (left - copyCharge) tail rest ht
            simp only [Nat.sub_zero, Nat.mul_add, Nat.mul_one] at hrst
            cases he
            simp only [hl, ↓reduceIte, Nat.mul_add]
            omega
          next _ => contradiction
        next hl =>
          cases h
          simp only [Nat.mul_add]
          omega
  next _ => contradiction

end LowSpaceSubsetSum.BudgetedJoinOne

end OAI
