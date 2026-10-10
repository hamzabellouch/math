import OAI.Analysis.MutuallyUnbiased.Bases.CompleteVanishing
import OAI.Analysis.MutuallyUnbiased.MixedMoments.MixedObstruction
import OAI.Analysis.MutuallyUnbiased.MixedSources.Main
import OAI.Analysis.MutuallyUnbiased.MixedTargets.Main
import OAI.Analysis.MutuallyUnbiased.Completion.Completion
import OAI.Analysis.MutuallyUnbiased.Bases.Families

namespace OAI

/-! Fourier vanishing and bounds on mutually unbiased bases, using actual mixed moments and the six-to-seven completion theorem. -/

noncomputable section

namespace MUB6

/-- Endpoint 2: seven mutually unbiased orthonormal bases in `ℂ⁶` cannot exist. -/
theorem no_seven_mutually_unbiased_bases : ¬Attainable 7 := by
  rintro ⟨B, hB⟩
  have hF := complete_family_fourier_zero B hB
  exact Certificate.MixedData.false_of_gram_interpretation B hB
    (Certificate.MixedSemantics.numericVector B)
    (Certificate.MixedSemantics.numericVector_abs_le_one B hB)
    (Certificate.MixedSemantics.numericVector_zero B)
    (Certificate.MixedSourceBridge.allRowsSound B hB hF)
    (Certificate.MixedTargetSemantics.rawGramIdentity B hB hF)

/-- Weiner completion in dimension six, preserving all six original bases. -/
theorem six_extend_to_seven : SixExtendToSeven :=
  Weiner.six_extend_to_seven

/-- Every finite family of mutually unbiased bases in `ℂ⁶` has size at most five. -/
theorem family_size_le_five (n : ℕ) (hn : Attainable n) : n ≤ 5 :=
  family_size_le_five_of_no_six
    (no_six_of_completion six_extend_to_seven no_seven_mutually_unbiased_bases) n hn

/-- Endpoint 3, with `N6` defined as the supremum of attainable family sizes. -/
theorem N6_le_five : N6 ≤ 5 :=
  N6_le_five_of_no_six
    (no_six_of_completion six_extend_to_seven no_seven_mutually_unbiased_bases)

end MUB6

end

end OAI
