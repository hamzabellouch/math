import OAI.Computability.PerfectCompleteness.Machines.BinaryGapReduction
import OAI.Computability.PerfectCompleteness.Reduction.FixedTargetValue

namespace OAI

section

namespace PerfectCompleteness.FixedBinaryGapReduction

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

def ofPreliminarySoundness
    (soundness : ∀ input, ¬BinaryLanguage.language input →
      FixedPreliminaryGame.value p input ≤ InitialParameters.epsilon δ) :
    BinaryGapReduction δ where
  alphabet := FixedTarget.alphabet p
  alphabet_ge_two := FixedTarget.alphabet_ge_two p
  construct := FixedTarget.construct p
  computation := FixedTarget.computation p
  finiteAlphabet := FixedTarget.finiteAlphabet p
  completeness := FixedTarget.value_eq_one p
  soundness input unsat := by
    have htarget := FixedTargetValue.value_le p input
    have hpreliminary := soundness input unsat
    have hpositive : 0 < (δ : ℝ) := by exact_mod_cast hδ
    unfold InitialParameters.epsilon at hpreliminary
    linarith

end
end PerfectCompleteness.FixedBinaryGapReduction

end

end OAI
