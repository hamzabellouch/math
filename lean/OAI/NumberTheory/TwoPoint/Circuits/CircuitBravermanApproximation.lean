import OAI.NumberTheory.TwoPoint.Circuits.CircuitNormBudget
import OAI.NumberTheory.TwoPoint.Circuits.CircuitDegreeBound

namespace OAI

/-! The combinatorial approximation stage of Braverman's proof, with a
fully explicit error circuit and coarse quantitative bounds. The depth
estimate is sufficient for the fixed-depth comparison. -/

namespace TwoPointCorrelations

theorem AC0Circuit.polynomial_error_approximation {n : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (hs : 1 ≤ s) (c : AC0Circuit n) :
    ∃ (P : BooleanCube n → ℝ) (E : AC0Circuit n),
      WalshDegreeLE P ((s * (Nat.log 2 c.size + 3)) ^ c.depth) ∧
      E.depth ≤ 4 * c.depth + 1 ∧
      E.size ≤ exceptionPolynomialBound c.size s * c.size ∧
      ν.probability (fun x => E.eval x = true) ≤ (c.size : ℝ) * (7 / 8 : ℝ) ^ s ∧
      (∀ x, E.eval x ≠ true → P x = c.indicator x) ∧
      ∀ x, |P x| ≤ (2 * ((c.size : ℝ) + 1) ^ 2) ^
        ((2 * (s * (Nat.log 2 c.size + 3)) + 2) ^ c.depth) := by
  let H := c.certificate ν s
  refine ⟨H.polynomial, H.error, ?_, H.error_depth, ?_, H.error_probability,
    H.exact_off_error, ?_⟩
  · exact H.degree_bound.mono (AC0Circuit.approximationDegree_le s hs c c.size le_rfl)
  · exact H.error_size.trans (AC0Circuit.exceptionSizeBound_le s c c.size le_rfl)
  · intro x
    exact (H.norm_bound x).trans (AC0Circuit.sampleNormBound_le s c c.size le_rfl)

end TwoPointCorrelations

end OAI
