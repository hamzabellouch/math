import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPowerExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PrimeTestCells

namespace OAI

/-! # Prime testing with executed scalar initialization

Both powers used by the test are produced by the doubling cursor. The
divisor scan consumes the computed limit directly and retains scalar state.
-/

namespace LowSpaceSubsetSum.WordSeedPrimeTestExecution

def run (ell : ℕ) (p : Fin (2^ell)) : (Bool × ℕ) × ℕ :=
  let modulus := WordSeedPowerExecution.run ell
  let limit := WordSeedPowerExecution.run ((ell+1)/2)
  let r := PrimeTestCells.scan p.val (limit.1-1) 2 0
  ((decide (modulus.1 ≤ 4*ell*p.val) && (decide (2 ≤ p.val) && r.1.1.isNone),
    12*r.1.2+modulus.2+limit.2+7), max 16 (r.2+16))

theorem run_value (ell : ℕ) (p : Fin (2^ell)) :
    (run ell p).1.1 = (SamplerAttempts.primeTest ell p).1 := by
  rw [← PrimeTestCells.test_value]
  simp only [run, WordSeedPowerExecution.run_value, PrimeTestCells.test,
    PrimeTestCells.divisors]

theorem run_work (ell : ℕ) (p : Fin (2^ell)) :
    (run ell p).1.2 ≤ 12*2^((ell+1)/2)+12*(ell+1) := by
  have h := SamplerAttempts.divisorsBits_tests ell p
  rw [← PrimeTestCells.divisors_value] at h
  dsimp only [PrimeTestCells.divisors] at h
  simp only [run, WordSeedPowerExecution.run_value, WordSeedPowerExecution.run_work]
  omega

theorem run_cells (ell : ℕ) (p : Fin (2^ell)) : (run ell p).2 = 28 := by
  simp only [run, PrimeTestCells.scan_cells]
  rfl

end LowSpaceSubsetSum.WordSeedPrimeTestExecution

end OAI
