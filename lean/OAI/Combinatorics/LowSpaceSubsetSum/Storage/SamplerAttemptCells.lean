import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PrimeTestCells

namespace OAI

/-! # Bounded rejection from an explicit candidate array

The immutable array is counted once. A tail cursor and two counters replace
the progressively shifted candidate function. The peak accumulator
includes the current evaluator's scratch space on every visited candidate.
-/

namespace LowSpaceSubsetSum.SamplerAttemptCells

variable {Ω : Type*}

def suffix (v : Array Ω) (offset fuel : ℕ) (h : offset+fuel ≤ v.size) : Fin fuel → Ω :=
  fun i => v[offset+i.val]'(by have := i.isLt; omega)

theorem suffix_zero (v : Array Ω) (offset fuel : ℕ) (h : offset+(fuel+1) ≤ v.size) :
    suffix v offset (fuel+1) h 0 = v[offset]'(by omega) := by
  simp only [suffix, Fin.val_zero, Nat.add_zero]

theorem suffix_succ (v : Array Ω) (offset fuel : ℕ) (h : offset+(fuel+1) ≤ v.size) :
    (fun i : Fin fuel => suffix v offset (fuel+1) h i.succ) =
      suffix v (offset+1) fuel (by omega) := by
  funext i
  simp only [suffix, Fin.val_succ]
  congr 1
  omega

def runAcc (test : Ω → (Bool × ℕ) × ℕ) (v : Array Ω) (wordCells : ℕ) :
    (fuel offset : ℕ) → offset+fuel ≤ v.size → ℕ → ℕ → ℕ → (Option Ω × ℕ × ℕ) × ℕ
  | 0, _, _, reads, work, peak => ((none, reads, work), max peak (v.size*wordCells+16))
  | fuel+1, offset, h, reads, work, peak =>
    let x := v[offset]'(by omega)
    let r := test x
    let peak' := max peak (v.size*wordCells+r.2+16)
    if r.1.1 then ((some x, reads+1, work+r.1.2), peak')
    else runAcc test v wordCells fuel (offset+1) (by omega)
      (reads+1) (work+r.1.2) peak'

theorem runAcc_value (test : Ω → (Bool × ℕ) × ℕ) (v : Array Ω) (wordCells : ℕ)
    (fuel offset : ℕ) (h : offset+fuel ≤ v.size) (reads work peak : ℕ) :
    (runAcc test v wordCells fuel offset h reads work peak).1 =
      SamplerAttempts.runCostAcc (fun x => (test x).1) fuel
        (suffix v offset fuel h) reads work := by
  induction fuel generalizing offset reads work peak with
  | zero => rfl
  | succ fuel ih =>
    simp only [runAcc, SamplerAttempts.runCostAcc, suffix_zero]
    split
    · rfl
    · rw [suffix_succ]
      exact ih _ _ _ _ _

theorem runAcc_cells (test : Ω → (Bool × ℕ) × ℕ) (v : Array Ω) (wordCells K : ℕ)
    (hK : ∀ x, (test x).2 ≤ K) (fuel offset : ℕ) (h : offset+fuel ≤ v.size)
    (reads work peak : ℕ) :
    (runAcc test v wordCells fuel offset h reads work peak).2 ≤
      max peak (v.size*wordCells+K+16) := by
  induction fuel generalizing offset reads work peak with
  | zero =>
    simp only [runAcc]
    exact max_le_max_left peak (by omega)
  | succ fuel ih =>
    have ht := hK (v[offset]'(by omega))
    simp only [runAcc]
    split
    · exact max_le_max_left peak (by omega)
    · exact (ih _ _ _ _ _).trans (by omega)

def run (test : Ω → (Bool × ℕ) × ℕ) (v : Array Ω) (wordCells : ℕ) :=
  runAcc test v wordCells v.size 0 (by omega) 0 0 0

theorem run_value (test : Ω → (Bool × ℕ) × ℕ) (v : Array Ω) (wordCells : ℕ) :
    (run test v wordCells).1 = SamplerAttempts.runCostAcc (fun x => (test x).1)
      v.size (fun i => v[i.val]) 0 0 := by
  rw [run, runAcc_value]
  congr 1
  funext i
  simp only [suffix, Nat.zero_add]

theorem run_cells (test : Ω → (Bool × ℕ) × ℕ) (v : Array Ω) (wordCells K : ℕ)
    (hK : ∀ x, (test x).2 ≤ K) :
    (run test v wordCells).2 ≤ v.size*wordCells+K+16 := by
  simpa only [run, Nat.zero_add, Nat.zero_max] using
    runAcc_cells test v wordCells K hK v.size 0 (by omega) 0 0 0

def range (D : ℕ) (v : Array (Fin (2^Nat.clog 2 D))) :=
  run (fun p => ((decide (rangeEligible D p), 0), 8)) v 1

theorem range_value (D : ℕ) (v : Array (Fin (2^Nat.clog 2 D))) :
    (range D v).1 = SamplerAttempts.runCostAcc
      (fun p => (decide (rangeEligible D p), 0)) v.size (fun i => v[i.val]) 0 0 := by
  exact run_value _ _ _

theorem range_cells (D : ℕ) (v : Array (Fin (2^Nat.clog 2 D))) :
    (range D v).2 ≤ v.size+24 := by
  simpa only [range, Nat.mul_one, Nat.add_assoc] using
    run_cells (fun p => ((decide (rangeEligible D p), 0), 8)) v 1 8 (fun _ => le_rfl)

def prime (ell : ℕ) (v : Array (Fin (2^ell))) := run (PrimeTestCells.test ell) v 1

theorem prime_value (ell : ℕ) (v : Array (Fin (2^ell))) :
    (prime ell v).1 = SamplerAttempts.runCostAcc (SamplerAttempts.primeTest ell)
      v.size (fun i => v[i.val]) 0 0 := by
  rw [prime, run_value]
  simp only [PrimeTestCells.test_value]

theorem prime_cells (ell : ℕ) (v : Array (Fin (2^ell))) :
    (prime ell v).2 ≤ v.size+40 := by
  simpa only [prime, Nat.mul_one, Nat.add_assoc] using
    run_cells (PrimeTestCells.test ell) v 1 24 (fun p => (PrimeTestCells.test_cells ell p).le)

end LowSpaceSubsetSum.SamplerAttemptCells

end OAI
