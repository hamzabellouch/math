import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Model.OperatorProperties

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.ProductModel

def IsCovariantFieldRepresentation (θ : ℕ → ℝ) (A : Hilbert →L[ℂ] Hilbert)
    (F : Base → Fiber →L[ℂ] Fiber) (B : ℝ) : Prop :=
  0 ≤ B ∧ (∀ x, ‖F x‖ ≤ B) ∧
    (∀ v : Fiber, StronglyMeasurable (fun x => F x v)) ∧
    (∀ f : Hilbert, A f =ᵐ[baseMeasure] fun x => F x (f x)) ∧
    (∀ᵐ x ∂baseMeasure,
      F (rotation θ x) =
        (WeightedShift.shift (-1)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap)

def centralDiagonalIntegral (F : Base → Fiber →L[ℂ] Fiber) : ℂ :=
  ∫ x, inner ℂ (lp.single 2 0 (1 : ℂ) : Fiber)
    (F x (lp.single 2 0 (1 : ℂ) : Fiber)) ∂baseMeasure

end Invariant233.ProductModel

end

end OAI
