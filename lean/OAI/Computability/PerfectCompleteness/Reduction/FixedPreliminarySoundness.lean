import OAI.Computability.PerfectCompleteness.Decoding.FixedStoppedUpperProbability
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedContradiction
import OAI.Computability.PerfectCompleteness.Reduction.FixedStoppedPair

namespace OAI

section

namespace PerfectCompleteness.FixedPreliminarySoundness

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)

theorem no_large_strategy (input : List Bool)
    (unsat : ¬ BinaryLanguage.language input)
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (hsuccess : InitialParameters.epsilon δ ≤
      (FixedPreliminaryGame.game parameters input).success strategy) : False := by
  obtain ⟨i, j, hij, hreserve⟩ := FixedStoppedPair.exists_pair parameters input strategy hsuccess
  have hupper := FixedStoppedUpperProbability.meeting_ge_gamma
    parameters i j hij input strategy hreserve
  have hsmall := FixedStoppedContradiction.meeting_lt_gamma
    parameters i j hij input strategy unsat
  exact (not_lt_of_ge hupper) hsmall

end
end PerfectCompleteness.FixedPreliminarySoundness

end

end OAI
