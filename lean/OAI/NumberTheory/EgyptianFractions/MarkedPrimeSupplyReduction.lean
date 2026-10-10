import OAI.NumberTheory.EgyptianFractions.MarkedReduction
import OAI.NumberTheory.EgyptianFractions.PrimeProductGrowth

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- For the actual prime-factorial multiplier, the size estimate and positivity
are theorems.  The remaining prerequisites are precisely the rational-divisor
supply and the quantitative marked prefix. -/
theorem quantitative_marked_length_of_prime_supply
    (hsupply : ∀ᶠ m : ℕ in atTop,
      HasRationalDivisorSupply m (markedSupplyMultiplier m) 16)
    (hprefix : ∀ᶠ m : ℕ in atTop,
      HasQuantitativeMarkedPrefix m (markedSupplyMultiplier m)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  exact quantitative_marked_length_of_supply_and_prefix markedSupplyMultiplier
    (Eventually.of_forall markedSupplyMultiplier_pos)
    eventually_log_markedSupplyMultiplier_le hsupply hprefix

end Problem337

end

end OAI
