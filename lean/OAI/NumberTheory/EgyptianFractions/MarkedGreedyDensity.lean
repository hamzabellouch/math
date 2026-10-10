import OAI.NumberTheory.EgyptianFractions.MarkedGreedy
import OAI.NumberTheory.EgyptianFractions.MarkedGroupingFin

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The concrete marked greedy trace obeys the unrestricted denominator chain. -/
theorem MarkedGreedySteps.denominator_chain {m R q Rf qf : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m R q L Rf qf) :
    GreedyDenominator m q → GreedyDenominator m qf := by
  induction h with
  | nil => exact id
  | cons R q n c L Rf qf hn hnm hnq heq hcq hcR hord tail ih =>
      intro hq
      exact ih (GreedyDenominator.mul hq (by omega) hnq)

/-- Every denominator arising from the marked prefix has divisors at every scale. -/
theorem MarkedGreedySteps.divisorDense {m R q : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m (m - 1) m L R q) (hm : 2 ≤ m) :
    DivisorDense m q :=
  (h.denominator_chain GreedyDenominator.base).divisorDense hm

/-- An abstract rational-divisor supply turns the marked prefix remainder into
an unmarked positive unit-fraction tail with the required grouping budget. -/
theorem MarkedGreedySteps.grouped_tail {m R q K B : ℕ} {L : List ℕ}
    (h : MarkedGreedySteps m (m - 1) m L R q) (hm : 2 ≤ m)
    (hK : 0 < K) (hRK : R * K ≤ q) (hsupply : HasRationalDivisorSupply m K B) :
    ∃ k : ℕ, ∃ n : Fin k → ℕ,
      (∀ i, 0 < n i) ∧ (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (R : ℚ) / q ∧
      (k : ℝ) ≤ (B : ℝ) *
        (Real.log ((R * K : ℕ) : ℝ) / (2 * Real.log (m : ℝ)) + 1) := by
  have hchain : GreedyDenominator m q := h.denominator_chain GreedyDenominator.base
  obtain ⟨k, n, hn, hsum, hlen⟩ := hchain.grouping_units_fin hm hK hRK hsupply
  refine ⟨k, n, hn, ?_, hlen⟩
  rw [hsum]
  have hKQ : (K : ℚ) ≠ 0 := by positivity
  push_cast
  exact mul_div_mul_right (R : ℚ) (q : ℚ) hKQ

end Problem337

end

end OAI
