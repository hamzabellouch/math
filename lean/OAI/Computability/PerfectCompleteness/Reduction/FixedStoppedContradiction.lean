import OAI.Computability.PerfectCompleteness.Decoding.DecoderFamilyLawLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedHighBound

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedContradiction

noncomputable section

attribute [local instance] FixedStoppedDecoderLaw.sampleFintype
  UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

theorem meeting_lt_gamma
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (unsat : ¬BinaryLanguage.language input) :
    (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.meeting parameters i j hij input) <
      FixedRankContradiction.gamma parameters (j.val + 1) := by
  apply lt_of_not_ge
  intro hupper
  exact FixedDecoderFamilyContradiction.impossible parameters
    (FixedStoppedDecoderContext.geometry parameters i j hij input) input
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (FixedStoppedDecoderLaw.useful parameters i j hij input strategy)
    parameters.plan.order parameters.plan.density
    (FixedStoppedDecoderContext.advice parameters i j hij input)
    (FixedStoppedDecoderContext.direction parameters i j hij input)
    (FixedStoppedDecoderLaw.threshold parameters j)
    (FixedStoppedDecoderContext.law parameters i j hij input)
    unsat (le_refl _) parameters.plan.density_pos
    (j.val + 1) (Nat.succ_le_of_lt j.isLt) hupper
    (FixedStoppedHighBound.probability_square_le parameters i j hij input strategy)

end
end PerfectCompleteness.FixedStoppedContradiction

end

end OAI
