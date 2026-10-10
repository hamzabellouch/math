import OAI.Probability.Localization.TerminalBudget

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

theorem finite_expected_regularization : FiniteEntropyStatement := by
  refine ⟨32,fun n hn Q P hP hac hK => ?_⟩
  let := hP
  have hn0 : 0 < n := by omega
  refine ⟨almost_sure_termination hn P Q hac hK,measurable_terminalLog hn0 P Q,?_,
    terminal_depth_integrable hn P Q hac hK,?_,?_,?_⟩
  · intro h hp
    exact ⟨(terminal_regular hn P Q hac hK h hp).1,(terminal_regular hn P Q hac hK h hp).2.1⟩
  · exact (terminal_attempts_budget hn P Q hac hK).1
  · exact (terminal_attempts_budget hn P Q hac hK).2
  · exact terminal_ennreal_budget hn P Q hac hK

end FiniteEntropy

end RepeatedLocalization

end OAI
