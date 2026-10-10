import OAI.NumberTheory.TotientAsymptotic.ShiftedDensity
import OAI.NumberTheory.TotientAsymptotic.PeriodicSieveCount
import OAI.NumberTheory.TotientAsymptotic.ShiftedSieveCount

namespace OAI

/-! An explicit local discrepancy bound for the actual shifted-prime sieve. -/
noncomputable section
namespace TotientAsymptotic

lemma shiftedPrimeSieve_rem_le (b X z : ℕ) (y : ℝ) (hy : 1 ≤ y) {d : ℕ}
    (hd : Squarefree d) :
    |BoundingSieve.rem (s := (shiftedPrimeSieve b X z y hy).toBoundingSieve) d| ≤ d+1 := by
  rw [BoundingSieve.rem,shiftedPrimeSieve_multSum]
  change |(((Finset.Icc 1 X).filter (fun q => d ∣ shiftedSievePolynomial b q)).card:ℝ)-
    shiftedSieveDensity b d*(X:ℝ)| ≤ d+1
  have he : (X:ℝ)/d*(Nat.count (fun q => d ∣ shiftedSievePolynomial b q) d:ℝ) =
      shiftedSieveDensity b d*(X:ℝ) := by
    rw [← shiftedRootCount_eq_count d b (Nat.pos_of_ne_zero hd.ne_zero),shiftedRootCount_density b d hd]
    field_simp [show (d:ℝ)≠0 by exact_mod_cast hd.ne_zero]
  rw [← he]
  exact shiftedSieve_interval_error b d (Nat.pos_of_ne_zero hd.ne_zero) X

end TotientAsymptotic

end

end OAI
