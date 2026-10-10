import OAI.NumberTheory.EgyptianFractions.ThreePrimeLocalDensity
import OAI.NumberTheory.EgyptianFractions.ThreePrimeSingularSeries

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- The normalized actual local unit-triple count at prime moduli, with one at
nonprime indices. The inactive branch makes this a total natural-indexed
function without imposing a finiteness instance on `ZMod 0`. -/
def threePrimeArithmeticFactor (p u : ℕ) : ℝ :=
  if hp : p.Prime then
    @threePrimeLocalFactor p ⟨hp.ne_zero⟩ (u : ZMod p)
  else 1

lemma threePrimeArithmeticFactor_of_prime (p u : ℕ) (hp : p.Prime) :
    threePrimeArithmeticFactor p u =
      if p ∣ u then 1 - 1 / ((p : ℝ) - 1) ^ 2
      else 1 + 1 / ((p : ℝ) - 1) ^ 3 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  simpa only [threePrimeArithmeticFactor, dite_eq_left hp] using
    threePrimeLocalFactor_natCast p u hp.two_le

lemma threePrimeArithmeticFactor_of_not_prime (p u : ℕ) (hp : ¬p.Prime) :
    threePrimeArithmeticFactor p u = 1 := by
  simp only [threePrimeArithmeticFactor, dite_eq_right hp]

/-- The analytically indexed odd-prime Euler factor is the normalized actual
count of its local unit solutions. -/
theorem threePrimeOddFactor_eq_arithmeticFactor (u n : ℕ) :
    1 + threePrimeOddPerturbation u n = threePrimeArithmeticFactor (n + 3) u := by
  by_cases hp : (n + 3).Prime
  · rw [threePrimeArithmeticFactor_of_prime _ _ hp]
    have hn : ((n + 3 : ℕ) : ℝ) - 1 = (n : ℝ) + 2 := by push_cast; ring
    rw [hn]
    simp only [threePrimeOddPerturbation, ite_eq_left hp]
    split_ifs <;> ring
  · simp [threePrimeOddPerturbation, hp,
      threePrimeArithmeticFactor_of_not_prime _ _ hp]

/-- The local unit-triple factor at two records precisely the parity obstruction. -/
theorem threePrimeArithmeticFactor_two (u : ℕ) :
    threePrimeArithmeticFactor 2 u = if Odd u then 2 else 0 := by
  rw [threePrimeArithmeticFactor_of_prime 2 u Nat.prime_two]
  have hdvd : 2 ∣ u ↔ ¬Odd u := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact not_iff_not.mp (by simp only [not_not, ZMod.natCast_ne_zero_iff_odd])
  by_cases hu : Odd u <;> norm_num [hdvd, hu]

/-- Exact interpretation of the singular series as the product of normalized
finite local unit-triple solution counts. -/
theorem threePrimeSingularSeries_eq_localProduct (u : ℕ) :
    threePrimeSingularSeries u = threePrimeArithmeticFactor 2 u *
      ∏' n : ℕ, threePrimeArithmeticFactor (n + 3) u := by
  rw [threePrimeSingularSeries, threePrimeArithmeticFactor_two]
  simp_rw [threePrimeOddFactor_eq_arithmeticFactor]

/-- The actual local-factor product converges, rather than merely being a
formal Euler-product notation. -/
theorem threePrimeArithmeticFactors_multipliable (u : ℕ) :
    Multipliable (fun n : ℕ => threePrimeArithmeticFactor (n + 3) u) := by
  simpa only [threePrimeOddFactor_eq_arithmeticFactor] using
    threePrimeOddFactors_multipliable u

end Problem337

end

end OAI
