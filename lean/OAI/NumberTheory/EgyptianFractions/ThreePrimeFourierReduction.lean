import OAI.NumberTheory.EgyptianFractions.ThreePrimeFourier
import OAI.NumberTheory.EgyptianFractions.ThreePrimeWeighted

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337.ThreePrimeFourier

/-- The ordinary positive-sign prime exponential sum, at the zero-padded
cyclic modulus `3*u+1`. -/
def primeFourierSum (u : ℕ) (r : ZMod (3 * u + 1)) : ℂ :=
  ∑ a ∈ (Finset.Icc 1 u).filter Nat.Prime,
    (Real.log (a : ℝ) : ℂ) * ZMod.stdAddChar ((a : ZMod (3 * u + 1)) * r)

/-- The cubic integrand extracting the ordered prime triples of sum `u`. -/
def primeFourierIntegrand (u : ℕ) (r : ZMod (3 * u + 1)) : ℂ :=
  primeFourierSum u r ^ 3 * ZMod.stdAddChar (-(u : ZMod (3 * u + 1)) * r)

/-- The canonical weighted count is exactly the real inverse Fourier sum. -/
theorem weightedSupplyPrimeTriples_eq_fourier (u : ℕ) :
    weightedSupplyPrimeTriples u =
      (∑ r, primeFourierIntegrand u r).re / (3 * u + 1 : ℕ) := by
  exact supply_prime_weighted_fourier_re u (by omega)

/-- The remaining quantitative three-prime assertion follows from explicit
major-frequency main terms and minor-frequency errors for the actual prime
exponential sums. This theorem does not assert either analytic estimate. -/
theorem quantitativeThreePrimeLowerBound_of_major_minor
    (major : (u : ℕ) → Finset (ZMod (3 * u + 1)))
    (c : ℝ) (hc : 0 < c)
    (hmajor : ∀ᶠ u : ℕ in atTop, Odd u →
      (2 * c * (u : ℝ) ^ 2) * (3 * u + 1 : ℕ) ≤
        (∑ r ∈ major u, primeFourierIntegrand u r).re)
    (hminor : ∀ᶠ u : ℕ in atTop, Odd u →
      ‖∑ r ∈ (major u)ᶜ, primeFourierIntegrand u r‖ ≤
        (c * (u : ℝ) ^ 2) * (3 * u + 1 : ℕ)) :
    QuantitativeThreePrimeLowerBound := by
  apply quantitativeThreePrimeLowerBound_of_weighted
  refine ⟨c, hc, ?_⟩
  filter_upwards [hmajor, hminor] with u hma hmi
  intro hu
  have h := supply_prime_weighted_lower_of_major_minor u (by omega : 3 * u < 3 * u + 1)
    (major u) (2 * c * (u : ℝ) ^ 2) (c * (u : ℝ) ^ 2) (hma hu) (hmi hu)
  change 2 * c * (u : ℝ) ^ 2 - c * (u : ℝ) ^ 2 ≤ weightedSupplyPrimeTriples u at h
  nlinarith

end Problem337.ThreePrimeFourier

end

end OAI
