import OAI.NumberTheory.Ostmann.Arithmetic.PrimePairHaarRegularity

namespace OAI

/-! # Regularity of the retained mixed-prime mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem continuous_correctedMixedPairAverage (P : PublishedProgressionInput) (Q q : ℕ)
    [NeZero q] (c : ℕ → ℕ → ℂ) :
    Continuous (correctedMixedPairAverage P Q q c) := by
  unfold correctedMixedPairAverage
  apply continuous_const.mul
  apply continuous_finsetSum
  intro z _
  exact continuous_const.mul (continuous_pageGiantWeight P Q q _)

end Ostmann

end OAI
