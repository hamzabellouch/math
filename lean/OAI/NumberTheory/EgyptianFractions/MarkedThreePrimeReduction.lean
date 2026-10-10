import OAI.NumberTheory.EgyptianFractions.MarkedFinalReduction
import OAI.NumberTheory.EgyptianFractions.RationalSupplyFromThreePrimes
import OAI.NumberTheory.EgyptianFractions.RationalDivisorSupplyBridge

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- The marked supply multiplier equals the prime-product supply integer. -/
lemma markedSupplyMultiplier_eq_supplyInteger (m : ℕ) :
    markedSupplyMultiplier m = supplyInteger (16 / Real.log 2) m := rfl

/-- The finite-indexed three-prime supply feeds the canonical list supply.
The quantitative three-prime lower bound remains an explicit hypothesis. -/
theorem eventual_marked_list_supply_of_three_primes
    (hthree : QuantitativeThreePrimeLowerBound) :
    ∀ᶠ m : ℕ in atTop,
      HasRationalDivisorSupply m (markedSupplyMultiplier m) 16 := by
  filter_upwards [eventual_marked_rational_supply_of_three_primes hthree] with m hm
  rw [markedSupplyMultiplier_eq_supplyInteger]
  exact rational_divisor_supply_bridge hm

/-- The quantitative marked-length bound follows from the explicit
quantitative three-prime lower bound. -/
theorem quantitative_marked_length_of_three_prime_lower_bound
    (hthree : QuantitativeThreePrimeLowerBound) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  exact quantitative_marked_length_of_eventual_prime_supply
    (eventual_marked_list_supply_of_three_primes hthree)

end Problem337

end

end OAI
