import OAI.NumberTheory.EgyptianFractions.RationalSupplyReduction
import OAI.NumberTheory.EgyptianFractions.SupplySize

namespace OAI
noncomputable section
open Filter
namespace Problem337

/-- The full rational-divisor supply, including the specified logarithmic
prime products and factorial fallback, follows from the one explicit
quantitative three-prime input. -/
theorem eventual_marked_rational_supply_of_three_primes
    (hthree : QuantitativeThreePrimeLowerBound) :
    ∀ᶠ m : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 →
      HasRationalDivisorSum (supplyInteger (16 / Real.log 2) m) (s : ℚ) 16 := by
  apply eventually_full_rational_supply_of_three_prime_lower_bound
    rationalSupplyBase (supplyInteger (16 / Real.log 2)) hthree
  · exact Filter.Eventually.of_forall (fun u =>
      ⟨primePrefixProduct_pos _, fourth_power_le_divisors_card_rationalSupplyBase u⟩)
  · refine ⟨8 / Real.log 2 + 1, ?_⟩
    simpa only [mul_assoc] using eventually_log_rationalSupplyBase_le
  · exact Filter.Eventually.of_forall (fun m u hu hum =>
      rationalSupplyBase_sq_dvd_supplyInteger hu hum)
  · exact eventually_small_dvd_supplyInteger (16 / Real.log 2)

/-- Simultaneous size and representation guarantees for the supply integer.
This does not assert the unproved three-prime hypothesis. -/
theorem marked_rational_supply_package_of_three_primes
    (hthree : QuantitativeThreePrimeLowerBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      m < supplyInteger (16 / Real.log 2) m ∧
      Real.log (supplyInteger (16 / Real.log 2) m : ℝ) ≤
        (32 / Real.log 2 + ε) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) ∧
      ∀ s : ℕ, 1 ≤ s → s ≤ m ^ 4 →
        HasRationalDivisorSum (supplyInteger (16 / Real.log 2) m) (s : ℚ) 16 := by
  have hrep := eventual_marked_rational_supply_of_three_primes hthree
  have hsize := eventual_marked_supply_size hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (hrep.and (hsize.and (eventually_ge_atTop 2)))
  refine ⟨max M 2, le_max_right _ _, ?_⟩
  intro m hm
  obtain ⟨hr, hs, hm2⟩ := hM m (le_trans (le_max_left _ _) hm)
  exact ⟨marked_supplyInteger_gt hm2, hs, hr⟩

end Problem337

end

end OAI
