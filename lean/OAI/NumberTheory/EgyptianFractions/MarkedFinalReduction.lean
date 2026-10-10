import OAI.NumberTheory.EgyptianFractions.MarkedPrimeSupplyReduction
import OAI.NumberTheory.EgyptianFractions.MarkedPrefixBridge

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- All arithmetic prefix, grouping, distinctness, and analytic length work is
proved.  The remaining input is the eventual rational-divisor supply for the
specific prime-factorial multiplier. -/
theorem quantitative_marked_length_of_eventual_prime_supply
    (hsupply : ∀ᶠ m : ℕ in atTop,
      HasRationalDivisorSupply m (markedSupplyMultiplier m) 16) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  apply quantitative_marked_length_of_prime_supply hsupply
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with m hm
  exact hasQuantitativeMarkedPrefix_of_le m (markedSupplyMultiplier m) hm
    (lt_markedSupplyMultiplier m (by omega)).le

end Problem337

end

end OAI
