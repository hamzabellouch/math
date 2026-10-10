import OAI.Computability.PerfectCompleteness.Machines.FixedBinaryGapReduction
import OAI.Computability.PerfectCompleteness.Reduction.FixedPreliminarySoundness
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryOutputLemmas

namespace OAI

section

namespace PerfectCompleteness.Theorem11

noncomputable section

theorem preliminary_value_le {δ : ℚ} {hδ : 0 < δ}
    (parameters : FixedParameters.Parameters δ hδ) (input : List Bool)
    (unsat : ¬BinaryLanguage.language input) :
    FixedPreliminaryGame.value parameters input ≤ InitialParameters.epsilon δ :=
  FixedPreliminaryValue.value_le_of_no_large_strategy parameters input
    (InitialParameters.epsilon δ) (fun strategy hsuccess =>
      FixedPreliminarySoundness.no_large_strategy parameters input unsat strategy hsuccess)

theorem exists_reduction (δ : ℚ) (positive : 0 < δ) (less_than_one : δ < 1) :
    Nonempty (BinaryGapReduction δ) := by
  obtain ⟨parameters⟩ := FixedParameters.exists_parameters positive less_than_one
  exact ⟨FixedBinaryGapReduction.ofPreliminarySoundness parameters
    (preliminary_value_le parameters)⟩

end
end PerfectCompleteness.Theorem11

end

end OAI
