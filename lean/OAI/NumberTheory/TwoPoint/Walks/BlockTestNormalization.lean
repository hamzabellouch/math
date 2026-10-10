import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace OAI

/-! Separate the retained block test's main term from its exceptional
fraction before applying the boundary-error estimate. -/

namespace TwoPointCorrelations

lemma block_test_normalization (L K T G R S M l δ : ℝ)
    (hL : L ≠ 0) (hM : M ≠ 0) :
    l * ((3 * R) * (l * (2 * M * S)) + (M * (2 * K * T) * G) * δ) /
        (2 * L * M) =
      3 * l ^ 2 * S * R / L + l * (K / L * G * T) * δ := by
  field_simp

end TwoPointCorrelations

end OAI
