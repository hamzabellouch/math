import OAI.Analysis.Cuntz.Quasitrace
import OAI.Analysis.Kaplansky.ActualAlgebra

namespace OAI

/-! Existence of a normalized two-quasitrace on the actual M48 algebra and a fixed positive contraction pair with universal real defect at least 1/144. -/

section

noncomputable section
namespace Kaplansky

theorem actual_normalizedTwoQuasitrace_exists :
    ∃ τ : OneQuasitrace ActualDefectAlgebra, τ.Normalized ∧ τ.IsTwo :=
  actualCuntzDimensionState.normalizedTwoQuasitrace_exists

theorem kaplansky_quasitrace_counterexample : MainTarget :=
  mainTarget_of_actualDefectQuasitrace actual_normalizedTwoQuasitrace_exists

end Kaplansky

end
end

end OAI
