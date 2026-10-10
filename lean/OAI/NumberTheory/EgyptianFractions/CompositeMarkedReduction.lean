import OAI.NumberTheory.EgyptianFractions.CompositeSupplySize
import OAI.NumberTheory.EgyptianFractions.MarkedPrefixBridge

namespace OAI
noncomputable section
open Filter

namespace Problem337.CompositeSupply

/-- The new fourth-power auxiliary integer can be passed directly to the
already proved marked construction.  Its positivity, size coefficient, and
marked greedy prefix are unconditional; precisely the arithmetic supply
remains as an explicit hypothesis here. -/
theorem quantitative_marked_length_of_supply
    (hsupply : ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  apply quantitative_marked_length_of_supply_and_prefix multiplier
    (Eventually.of_forall multiplier_pos) eventually_log_multiplier_le hsupply
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with m hm
  exact hasQuantitativeMarkedPrefix_of_le m (multiplier m) hm
    (marker_lt_multiplier m (by omega)).le

end Problem337.CompositeSupply

end

end OAI
