import Mathlib
import OAI.Analysis.BrownMeasure.Determinant
import OAI.Analysis.BrownMeasure.Dirac
import OAI.Analysis.BrownMeasure.Orbit
import OAI.Analysis.BrownMeasure.Resolvent
import OAI.Analysis.FiniteFactor.Main

namespace OAI

noncomputable section
open MeasureTheory
namespace FiniteFactor

theorem productBrown : ProductBrownClaim := by
  intro θ hθ
  refine ⟨inferInstance, dirac_zero_support_compact, ?_⟩
  intro z
  rw [expLogPotential_dirac_zero]
  by_cases hz : z = 0
  · subst z
    simp only [map_zero, sub_zero, norm_zero, ENNReal.ofReal_zero]
    exact sourceOperator_determinant_zero θ hθ
  · exact sourceResolvent_determinant θ hθ hz
end FiniteFactor

end

end OAI
