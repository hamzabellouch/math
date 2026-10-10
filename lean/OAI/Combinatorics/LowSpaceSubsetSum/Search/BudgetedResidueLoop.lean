import OAI.Combinatorics.LowSpaceSubsetSum.Separators.BudgetedSeparatorFlow

namespace OAI

/-! # Tail-recursive residue enumeration with one shared budget

The loop keeps a residue counter and releases each completed bucket before
starting its successor. The work accumulator avoids return frames.
-/

namespace LowSpaceSubsetSum.BudgetedResidueLoop

open BudgetedSeparatorFlow

def reference (bucket : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => false
  | z, remaining + 1 => if bucket z then true else reference bucket (z + 1) remaining

def loop (bucket : ℕ → ℕ → Option (Bool × ℕ) × ℕ) :
    ℕ → ℕ → ℕ → ℕ → Option (Bool × ℕ) × ℕ
  | z, remaining, budget, work =>
    if 4 ≤ budget then
      match remaining with
      | 0 => (some (false, budget - 4), work + 1)
      | remaining + 1 =>
        let out := bucket z (budget - 4)
        match out.1 with
        | none => (none, work + out.2 + 2)
        | some (true, left) => (some (true, left), work + out.2 + 3)
        | some (false, left) => loop bucket (z + 1) remaining left (work + out.2 + 3)
    else (none, work + 1)

def run (bucket : ℕ → ℕ → Option (Bool × ℕ) × ℕ) (z remaining budget : ℕ) :=
  loop bucket z remaining budget 0

def allowance (bill : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 4
  | z, remaining + 1 => 4 + bill z + allowance bill (z + 1) remaining

theorem allowance_eq (bill : ℕ → ℕ) (z count : ℕ) :
    allowance bill z count = 4 * (count + 1) +
      ((List.range count).map (fun i => bill (z + i))).sum := by
  induction count generalizing z with
  | zero => simp [allowance]
  | succ count ih =>
    rw [allowance, ih, List.sum_range_succ']
    simp only [Nat.add_zero, Nat.succ_eq_add_one]
    have he : (fun i => bill (z + (i + 1))) = (fun i => bill (z + 1 + i)) := by
      funext i
      congr 1
      omega
    rw [he]
    omega

theorem loop_account (bucket : ℕ → ℕ → Option (Bool × ℕ) × ℕ)
    (hb : ∀ z budget, Account budget (bucket z budget))
    (z remaining budget work : ℕ) :
    (loop bucket z remaining budget work).2 ≤ work + budget + 1 ∧
      ∀ v left, (loop bucket z remaining budget work).1 = some (v, left) →
        left ≤ budget ∧ (loop bucket z remaining budget work).2 ≤ work + (budget - left) := by
  induction remaining generalizing z budget work with
  | zero =>
    rw [loop]
    split
    next hbudget =>
      constructor
      · dsimp only; omega
      · intro v left h
        cases h
        dsimp only
        omega
    next hbudget =>
      constructor
      · dsimp only; omega
      · intro v left h
        contradiction
  | succ remaining ih =>
    rw [loop]
    split
    next hbudget =>
      dsimp only
      generalize he : bucket z (budget - 4) = out
      have ho := hb z (budget - 4)
      rw [he] at ho
      have hw := ho.1
      cases hv : out.1 with
      | none =>
        dsimp only
        constructor
        · omega
        · intro v left h
          contradiction
      | some p =>
        rcases p with ⟨v, left⟩
        have hs := ho.2 v left hv
        cases v
        · dsimp only
          have hi := ih (z + 1) left (work + out.2 + 3)
          constructor
          · omega
          · intro v rest h
            have hh := hi.2 v rest h
            omega
        · dsimp only
          constructor
          · omega
          · intro v rest h
            cases h
            omega
    next hbudget =>
      constructor
      · dsimp only; omega
      · intro v left h
        contradiction

theorem account (bucket : ℕ → ℕ → Option (Bool × ℕ) × ℕ)
    (hb : ∀ z budget, Account budget (bucket z budget)) (z remaining budget : ℕ) :
    Account budget (run bucket z remaining budget) := by
  simpa only [run, Account, Nat.zero_add] using loop_account bucket hb z remaining budget 0

theorem value (bucket : ℕ → ℕ → Option (Bool × ℕ) × ℕ) (pureBucket : ℕ → Bool)
    (hv : ∀ z budget v left, (bucket z budget).1 = some (v, left) → v = pureBucket z)
    (z remaining budget work : ℕ) (v : Bool) (left : ℕ)
    (h : (loop bucket z remaining budget work).1 = some (v, left)) :
    v = reference pureBucket z remaining := by
  induction remaining generalizing z budget work v left with
  | zero =>
    rw [loop] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ remaining ih =>
    rw [loop] at h
    split at h
    next hbudget =>
      cases he : (bucket z (budget - 4)).1 with
      | none => simp only [he] at h; contradiction
      | some p =>
        rcases p with ⟨v', rest⟩
        have heq := hv z (budget - 4) v' rest he
        cases v'
        · simp only [he] at h
          have hi := ih (z + 1) rest (work + (bucket z (budget - 4)).2 + 3) v left h
          simpa only [reference, ← heq, Bool.false_eq_true, ↓reduceIte] using hi
        · simp only [he] at h
          cases h
          simp only [reference, ← heq, ↓reduceIte]
    next hbudget => contradiction

theorem remaining (bucket : ℕ → ℕ → Option (Bool × ℕ) × ℕ) (bill : ℕ → ℕ)
    (hr : ∀ z budget v left, (bucket z budget).1 = some (v, left) → budget ≤ left + bill z)
    (z count budget work : ℕ) (v : Bool) (left : ℕ)
    (h : (loop bucket z count budget work).1 = some (v, left)) :
    budget ≤ left + allowance bill z count := by
  induction count generalizing z budget work v left with
  | zero =>
    rw [loop] at h
    split at h
    · cases h; simp only [allowance]; omega
    · contradiction
  | succ count ih =>
    rw [loop] at h
    split at h
    next hbudget =>
      cases he : (bucket z (budget - 4)).1 with
      | none => simp only [he] at h; contradiction
      | some p =>
        rcases p with ⟨v', rest⟩
        have hb := hr z (budget - 4) v' rest he
        cases v'
        · simp only [he] at h
          have hi := ih (z + 1) rest (work + (bucket z (budget - 4)).2 + 3) v left h
          simp only [allowance]
          omega
        · simp only [he] at h
          cases h
          simp only [allowance]
          omega
    next hbudget => contradiction

theorem complete (bucket : ℕ → ℕ → Option (Bool × ℕ) × ℕ) (bill : ℕ → ℕ)
    (hc : ∀ z budget, bill z ≤ budget → ∃ v left, (bucket z budget).1 = some (v, left))
    (hr : ∀ z budget v left, (bucket z budget).1 = some (v, left) → budget ≤ left + bill z)
    (z count budget work : ℕ) (hb : allowance bill z count ≤ budget) :
    ∃ v left, (loop bucket z count budget work).1 = some (v, left) := by
  induction count generalizing z budget work with
  | zero =>
    have hh : 4 ≤ budget := hb
    exact ⟨false, budget - 4, by rw [loop, ite_eq_left hh]⟩
  | succ count ih =>
    have hh : 4 ≤ budget := by simp only [allowance] at hb; omega
    have hbill : bill z ≤ budget - 4 := by simp only [allowance] at hb; omega
    obtain ⟨v, left, he⟩ := hc z (budget - 4) hbill
    have hrest := hr z (budget - 4) v left he
    cases v
    · obtain ⟨v', rest, hi⟩ := ih (z + 1) left (work + (bucket z (budget - 4)).2 + 3)
        (by simp only [allowance] at hb; omega)
      exact ⟨v', rest, by rw [loop, ite_eq_left hh]; simpa only [he] using hi⟩
    · exact ⟨true, left, by rw [loop, ite_eq_left hh]; simp only [he]⟩

end LowSpaceSubsetSum.BudgetedResidueLoop

end OAI
