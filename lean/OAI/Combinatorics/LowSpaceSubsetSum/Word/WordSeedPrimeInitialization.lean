import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedScalarExecution

namespace OAI

/-! # Executed prime-modulus initialization from its known width -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

def primeInitialized (w n ell : ℕ) (hell : 4 ≤ ell) (hw : ell ≤ w) :
    Execution (WordSeedRealization.prime w n ell hell hw) where
  run stream cursor :=
    let modulus := WordSeedPowerExecution.run ell
    let r := (prime w n ell hell hw modulus.1
      (WordSeedPowerExecution.run_value ell)).run stream cursor
    ⟨r.accepted,r.cursor,modulus.2+r.work+1,max 16 (r.cells+8),r.retained⟩
  value stream cursor :=
    (prime w n ell hell hw (WordSeedPowerExecution.run ell).1
      (WordSeedPowerExecution.run_value ell)).value stream cursor

theorem primeInitialized_bounded (w n ell : ℕ) (hell : 4 ≤ ell) (hw : ell ≤ w) :
    (primeInitialized w n ell hell hw).Bounded
      (n^3*(12*2^((ell+1)/2)+12*(ell+1)+11)+3*ell+17)
      (2*n^3+124) (n^3+18) := by
  intro stream cursor
  have h := prime_bounded w n ell hell hw (WordSeedPowerExecution.run ell).1
    (WordSeedPowerExecution.run_value ell) stream cursor
  dsimp only [primeInitialized]
  rw [WordSeedPowerExecution.run_work]
  exact ⟨by omega,max_le (by omega) (by omega),h.2.2⟩

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
