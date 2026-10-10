import OAI.Analysis.IrrationalRotation.Model.FieldDiagonal

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def fieldOperator (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x, ‖a x‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ :=
  (shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
    fieldDiagonal a C hC ha hm

def fieldTailProjection (m : ℤ) : Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ :=
  (tailProjection m).compLpL 2 μ

end Invariant233.WeightedShift

end

end OAI
