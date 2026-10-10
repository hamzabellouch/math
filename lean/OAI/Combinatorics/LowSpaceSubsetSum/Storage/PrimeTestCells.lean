import OAI.Combinatorics.LowSpaceSubsetSum.Counting.SamplerAttempts

namespace OAI

/-! # Scalar-cursor trial division

The cursor advances by one after a failed divisor test. The loop retains
only its fixed scalar state; the candidate enumeration is not materialized.
Its returned answer and counter equal the trial-division specification.
-/

namespace LowSpaceSubsetSum.PrimeTestCells

def scan (p : ℕ) : ℕ → ℕ → ℕ → (Option ℕ × ℕ) × ℕ
  | 0, _, used => ((none, used), 12)
  | fuel+1, next, used =>
    if next*next ≤ p ∧ p % next = 0 then ((some next, used+1), 12)
    else scan p fuel (next+1) (used+1)

theorem scan_value (p fuel next used : ℕ) :
    (scan p fuel next used).1 =
      SamplerAttempts.runAcc (fun d => d*d ≤ p ∧ p%d = 0) fuel
        (fun i => next+i.val) used := by
  induction fuel generalizing next used with
  | zero => rfl
  | succ fuel ih =>
    change (if next*next ≤ p ∧ p%next = 0 then ((some next, used+1), 12)
      else scan p fuel (next+1) (used+1)).1 =
        if next*next ≤ p ∧ p%next = 0 then (some next, used+1)
        else SamplerAttempts.runAcc (fun d => d*d ≤ p ∧ p%d = 0) fuel
          (fun i => next+i.val.succ) (used+1)
    by_cases h : next*next ≤ p ∧ p%next = 0
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h]
      rw [ih]
      congr 1
      funext i
      omega

theorem scan_cells (p fuel next used : ℕ) : (scan p fuel next used).2 = 12 := by
  induction fuel generalizing next used with
  | zero => rfl
  | succ fuel ih =>
    rw [scan]
    split
    · rfl
    · exact ih _ _

def divisors (ell : ℕ) (p : Fin (2^ell)) : (Option ℕ × ℕ) × ℕ :=
  scan p.val (2^((ell+1)/2)-1) 2 0

theorem divisors_value (ell : ℕ) (p : Fin (2^ell)) :
    (divisors ell p).1 = SamplerAttempts.divisorsBits ell p := by
  rw [divisors, scan_value]
  unfold SamplerAttempts.divisorsBits SamplerAttempts.run
  congr 1
  funext i
  omega

def test (ell : ℕ) (p : Fin (2^ell)) : (Bool × ℕ) × ℕ :=
  let r := divisors ell p
  ((decide (2^ell ≤ 4*ell*p.val) && (decide (2 ≤ p.val) && r.1.1.isNone), r.1.2),
    r.2+12)

theorem test_value (ell : ℕ) (p : Fin (2^ell)) :
    (test ell p).1 = SamplerAttempts.primeTest ell p := by
  simp only [test, divisors_value, SamplerAttempts.primeTest]

theorem test_cells (ell : ℕ) (p : Fin (2^ell)) : (test ell p).2 = 24 := by
  simp only [test, divisors, scan_cells]

end LowSpaceSubsetSum.PrimeTestCells

end OAI
