import OAI.Combinatorics.EditApproximation.Refinement.ComputedPreparedInputBounds
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRefinementWords

namespace OAI

namespace EditApproximation
open Filter

/-- The numeric record is inhabited by the actual constructed scalar words. -/
theorem computedPreparedWords_numeric :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny : ℕ, nx + ny ≤ N → ∀ t : ℕ, t ≤ inputHeight N ^ 2 →
      ∀ (pass : ℕ) (word : List Bool) (hpositive : 0 < bitWordValue word),
      bitWordValue word = inputSmallLog N → word.length ≤ Nat.size (inputSmallLog N) →
      ∀ integer : ℕ → TargetInterval ny → ℕ,
      (∀ b r, Nat.size (integer b r) ≤ inputHeight N) →
      let values := (refinementParameterWordsWithWork N pass word hpositive).1
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t
        values.tau values.factor values.eta values.kappa values.delta integer := by
  filter_upwards [computedPreparedNumericBounds,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hn hell
  intro nx ny hsize t ht pass word hpositive hvalue hwidth integer hint
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hw := computedRefinementWords_bounds N pass word hvalue hwidth hH hpositive
  exact hn nx ny hsize t ht _ _ _ _ _ hw.1 hw.2.1 hw.2.2.1 hw.1 hw.2.2.2.1
    hw.2.2.2.2.1 hw.2.2.2.2.2 integer hint

end EditApproximation

end OAI
