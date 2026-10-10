import OAI.NumberTheory.EgyptianFractions.DivisorDensity
import OAI.NumberTheory.EgyptianFractions.MarkedGroupingUnits

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- Fin-indexed form of the marked grouping construction, for expansion assembly. -/
theorem marked_grouping_units_fin (m q K B X : ℕ) (hm : 2 ≤ m)
    (hq : 0 < q) (hK : 0 < K) (hXq : X ≤ q)
    (hdensity : HasMarkedDivisorDensity m q)
    (hsupply : HasRationalDivisorSupply m K B) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      (∀ i, 0 < n i) ∧
      (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (X : ℚ) / ((q : ℚ) * K) ∧
      (k : ℝ) ≤ (B : ℝ) * (Real.log (X : ℝ) / (2 * Real.log (m : ℝ)) + 1) := by
  obtain ⟨den, hlen, hpos, hsum⟩ := marked_grouping_units_from_list_supply m q K B X hm hq hK hXq hdensity hsupply
  refine ⟨den.length, den.get, fun i => hpos _ (List.get_mem den i), ?_, hlen⟩
  rw [← List.sum_ofFn]
  change (List.ofFn ((fun n : ℕ => (1 : ℚ) / (n : ℚ)) ∘ den.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]
  exact hsum

/-- Apply marked grouping to an unreduced greedy denominator. -/
theorem GreedyDenominator.grouping_units_fin {m q K B X : ℕ}
    (hq : GreedyDenominator m q) (hm : 2 ≤ m) (hK : 0 < K) (hXq : X ≤ q)
    (hsupply : HasRationalDivisorSupply m K B) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      (∀ i, 0 < n i) ∧
      (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (X : ℚ) / ((q : ℚ) * K) ∧
      (k : ℝ) ≤ (B : ℝ) * (Real.log (X : ℝ) / (2 * Real.log (m : ℝ)) + 1) :=
  marked_grouping_units_fin m q K B X hm (hq.positive (by omega)) hK hXq
    (hq.divisorDense hm) hsupply

end Problem337

end

end OAI
