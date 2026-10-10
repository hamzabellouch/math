import OAI.Combinatorics.LowSpaceSubsetSum.Counting.RejectionSamplerCoupling
import Mathlib.Data.Nat.Sqrt

namespace OAI

/-! # Counted bounded rejection and deterministic divisor tests

The accumulator counts precisely the candidates actually read, including
rejections. It is carried through tail calls and never revisits a candidate.
-/

namespace LowSpaceSubsetSum

namespace SamplerAttempts

variable {Ω : Type*}

def runAcc (A : Ω → Prop) [DecidablePred A] :
    (N : ℕ) → (Fin N → Ω) → ℕ → Option Ω × ℕ
  | 0, _, used => (none, used)
  | N + 1, f, used => if A (f 0) then (some (f 0), used + 1)
      else runAcc A N (fun i => f i.succ) (used + 1)

def run (A : Ω → Prop) [DecidablePred A] (N : ℕ) (f : Fin N → Ω) : Option Ω × ℕ :=
  runAcc A N f 0

theorem runAcc_value (A : Ω → Prop) [DecidablePred A]
    (N : ℕ) (f : Fin N → Ω) (used : ℕ) :
    (runAcc A N f used).1 = firstAccept A N f := by
  induction N generalizing used with
  | zero => rfl
  | succ N ih =>
    simp only [runAcc, firstAccept]
    split
    · rfl
    · exact ih _ _

theorem run_value (A : Ω → Prop) [DecidablePred A] (N : ℕ) (f : Fin N → Ω) :
    (run A N f).1 = firstAccept A N f := runAcc_value A N f 0

theorem runAcc_reads (A : Ω → Prop) [DecidablePred A]
    (N : ℕ) (f : Fin N → Ω) (used : ℕ) :
    used ≤ (runAcc A N f used).2 ∧ (runAcc A N f used).2 ≤ used + N := by
  induction N generalizing used with
  | zero => simp [runAcc]
  | succ N ih =>
    simp only [runAcc]
    split
    · simp
    · have h := ih (fun i => f i.succ) (used + 1)
      omega

theorem run_reads (A : Ω → Prop) [DecidablePred A] (N : ℕ) (f : Fin N → Ω) :
    (run A N f).2 ≤ N := by
  simpa only [run, Nat.zero_add] using (runAcc_reads A N f 0).2

theorem runAcc_exhausted (A : Ω → Prop) [DecidablePred A]
    (N : ℕ) (f : Fin N → Ω) (used : ℕ) (h : firstAccept A N f = none) :
    (runAcc A N f used).2 = used + N := by
  induction N generalizing used with
  | zero => simp [runAcc]
  | succ N ih =>
    have hf := (firstAccept_eq_none_iff A (N + 1) f).mp h
    have h0 := hf 0
    simp only [runAcc, h0, ↓reduceIte]
    have ht := (firstAccept_eq_none_iff A N (fun i => f i.succ)).mpr (fun i => hf i.succ)
    simpa only [Nat.add_assoc, Nat.add_comm 1 N] using ih _ (used + 1) ht

theorem range_reads (D n : ℕ) (f : Fin (n ^ 3) → Fin (2 ^ Nat.clog 2 D)) :
    (run (rangeEligible D) (n ^ 3) f).2 ≤ n ^ 3 := run_reads _ _ _

theorem prime_reads (ell n : ℕ) (f : Fin (n ^ 3) → Fin (2 ^ ell)) :
    (run (primeEligible ell) (n ^ 3) f).2 ≤ n ^ 3 := run_reads _ _ _

/-- Search each possible small divisor once, stopping at the first divisor.
The numeric square-root bound is a parameter to this counted inner loop. -/
def divisors (p : ℕ) : Option ℕ × ℕ :=
  run (fun d => p % d = 0) (Nat.sqrt p - 1) (fun i => i.val + 2)

def isPrime (p : ℕ) : Bool := decide (2 ≤ p) && (divisors p).1.isNone

theorem isPrime_correct (p : ℕ) : isPrime p = true ↔ p.Prime := by
  rw [isPrime, Bool.and_eq_true, decide_eq_true_eq]
  have hn : (divisors p).1.isNone = true ↔
      ∀ d, 2 ≤ d → d ≤ Nat.sqrt p → ¬d ∣ p := by
    rw [Option.isNone_iff_eq_none]
    unfold divisors
    rw [run_value, firstAccept_eq_none_iff]
    constructor
    · intro h d hd hs hdiv
      have hi : d - 2 < Nat.sqrt p - 1 := by omega
      have hx := h ⟨d - 2, hi⟩
      simp only at hx
      rw [show d - 2 + 2 = d by omega] at hx
      exact hx (Nat.mod_eq_zero_of_dvd hdiv)
    · intro h i hmod
      have hi := i.isLt
      exact h (i.val + 2) (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hmod)
  rw [hn, Nat.prime_def_le_sqrt]

theorem divisor_tests_le (p : ℕ) : (divisors p).2 ≤ Nat.sqrt p :=
  (run_reads _ _ _).trans (Nat.sub_le _ _)

theorem divisor_tests_lt_pow {p ell : ℕ} (hp : p < 2 ^ ell) :
    (divisors p).2 < 2 ^ ((ell + 1) / 2) := by
  apply (divisor_tests_le p).trans_lt
  apply Nat.sqrt_lt'.mpr
  apply hp.trans_le
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The candidate evaluator returns its Boolean answer and its actual work.
Both work counters are accumulator fields, including on exhaustion. -/
def runCostAcc (test : Ω → Bool × ℕ) :
    (N : ℕ) → (Fin N → Ω) → ℕ → ℕ → Option Ω × ℕ × ℕ
  | 0, _, reads, work => (none, reads, work)
  | N + 1, f, reads, work =>
    let result := test (f 0)
    if result.1 then (some (f 0), reads + 1, work + result.2)
    else runCostAcc test N (fun i => f i.succ) (reads + 1) (work + result.2)

theorem runCostAcc_value (test : Ω → Bool × ℕ)
    (N : ℕ) (f : Fin N → Ω) (reads work : ℕ) :
    (runCostAcc test N f reads work).1 = firstAccept (fun a => (test a).1 = true) N f := by
  induction N generalizing reads work with
  | zero => rfl
  | succ N ih =>
    simp only [runCostAcc, firstAccept]
    split
    · rfl
    · exact ih _ _ _

theorem runCostAcc_bounds (test : Ω → Bool × ℕ) (K : ℕ)
    (hK : ∀ a, (test a).2 ≤ K)
    (N : ℕ) (f : Fin N → Ω) (reads work : ℕ) :
    (runCostAcc test N f reads work).2.1 ≤ reads + N ∧
      (runCostAcc test N f reads work).2.2 ≤ work + N * K := by
  induction N generalizing reads work with
  | zero => simp [runCostAcc]
  | succ N ih =>
    simp only [runCostAcc]
    split
    · simp only
      constructor
      · omega
      · rw [Nat.succ_mul]
        have := hK (f 0)
        omega
    · have h := ih (fun i => f i.succ) (reads + 1) (work + (test (f 0)).2)
      have := hK (f 0)
      constructor
      · omega
      · apply h.2.trans
        rw [Nat.succ_mul]
        omega

/-- A bit-bounded trial-division implementation. The loop bound is a power
of two determined by the candidate width, so no square-root oracle is used.
Squares beyond the candidate are discarded by an ordinary multiplication
and comparison before divisibility is tested. -/
def divisorsBits (ell : ℕ) (p : Fin (2 ^ ell)) : Option ℕ × ℕ :=
  run (fun d => d * d ≤ p.val ∧ p.val % d = 0)
    (2 ^ ((ell + 1) / 2) - 1) (fun i => i.val + 2)

theorem divisorsBits_none (ell : ℕ) (p : Fin (2 ^ ell)) :
    (divisorsBits ell p).1.isNone = true ↔
      ∀ d, 2 ≤ d → d ≤ Nat.sqrt p.val → ¬d ∣ p.val := by
  rw [Option.isNone_iff_eq_none]
  unfold divisorsBits
  rw [run_value, firstAccept_eq_none_iff]
  have hsqrt : Nat.sqrt p.val < 2 ^ ((ell + 1) / 2) := by
    apply Nat.sqrt_lt'.mpr
    apply p.isLt.trans_le
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · intro h d hd hs hdiv
    have hi : d - 2 < 2 ^ ((ell + 1) / 2) - 1 := by omega
    have hx := h ⟨d - 2, hi⟩
    simp only at hx
    rw [show d - 2 + 2 = d by omega] at hx
    exact hx ⟨Nat.le_sqrt.mp hs, Nat.mod_eq_zero_of_dvd hdiv⟩
  · intro h i hi
    exact h (i.val + 2) (by omega) (Nat.le_sqrt.mpr hi.1)
      (Nat.dvd_of_mod_eq_zero hi.2)

theorem divisorsBits_tests (ell : ℕ) (p : Fin (2 ^ ell)) :
    (divisorsBits ell p).2 ≤ 2 ^ ((ell + 1) / 2) :=
  (run_reads _ _ _).trans (Nat.sub_le _ _)

def primeTest (ell : ℕ) (p : Fin (2 ^ ell)) : Bool × ℕ :=
  let result := divisorsBits ell p
  (decide (2 ^ ell ≤ 4 * ell * p.val) &&
    (decide (2 ≤ p.val) && result.1.isNone), result.2)

theorem primeTest_correct (ell : ℕ) (p : Fin (2 ^ ell)) :
    (primeTest ell p).1 = true ↔ primeEligible ell p := by
  simp only [primeTest, Bool.and_eq_true, decide_eq_true_eq, divisorsBits_none,
    primeEligible, primeRange, Finset.mem_filter, Nat.mem_primesLE]
  rw [← Nat.prime_def_le_sqrt]
  have hp := p.isLt.le
  tauto

def primeRun (ell n : ℕ) (f : Fin (n ^ 3) → Fin (2 ^ ell)) :=
  runCostAcc (primeTest ell) (n ^ 3) f 0 0

theorem primeRun_value (ell n : ℕ) (f : Fin (n ^ 3) → Fin (2 ^ ell)) :
    (primeRun ell n f).1 = firstAccept (primeEligible ell) (n ^ 3) f := by
  rw [primeRun, runCostAcc_value]
  congr 1
  funext p
  exact propext (primeTest_correct ell p)

theorem primeRun_bounds (ell n : ℕ) (f : Fin (n ^ 3) → Fin (2 ^ ell)) :
    (primeRun ell n f).2.1 ≤ n ^ 3 ∧
      (primeRun ell n f).2.2 ≤ n ^ 3 * 2 ^ ((ell + 1) / 2) := by
  simpa only [primeRun, Nat.zero_add] using
    runCostAcc_bounds (primeTest ell) _
      (fun p => divisorsBits_tests ell p) (n ^ 3) f 0 0

end SamplerAttempts
end LowSpaceSubsetSum

end OAI
