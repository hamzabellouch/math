import OAI.Analysis.IrrationalRotation.Model.ContinuousConstruction

namespace OAI

noncomputable section
open scoped ENNReal

namespace Invariant233.CircleParameterData

def extendedContinuousCost (p : CircleParameterData) (θ : ℝ)
    (d : BackgroundBumpData θ) : Circle → ℝ≥0∞ :=
  Function.update (fun x => ENNReal.ofReal (p.continuousCost θ d x)) 0 ∞

end Invariant233.CircleParameterData

end

end OAI
