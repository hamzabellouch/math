import OAI.Analysis.IrrationalRotation.Model.Rotation
import OAI.Analysis.IrrationalRotation.Model.FieldUnboundedMultiplier

namespace OAI

noncomputable section
namespace Invariant233.Rotation

def exponentialTransfer (θ : ℝ) (b : Circle → ℝ) : Hilbert →ₗ.[ℂ] Hilbert :=
  WeightedShift.fieldUnboundedMultiplier circleMeasure
    (fun x k => (Real.exp (b (action θ k x)) : ℂ))

end Invariant233.Rotation

end

end OAI
