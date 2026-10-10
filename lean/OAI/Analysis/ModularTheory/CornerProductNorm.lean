import OAI.Analysis.ModularTheory.CornerGNSActions
import OAI.Analysis.ModularTheory.TracialCompression
import OAI.Analysis.OperatorAlgebra.GNSProductNorm

namespace OAI

/-! Finite sums of actual corner products have their finite-tracial GNS norm. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local irreducible] modularCompressedTracialState

lemma modularCornerProduct_right_support (S : StandardModularData H) (n : ℕ)
    (a b : (modularCompressedCorner S n).toStarSubalgebra) :
    (isometricCornerLift (modularCornerInclusion (H := H) n) a.val *
      modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) n) b.val)) *
      modularTracialCornerProjection S n =
    isometricCornerLift (modularCornerInclusion (H := H) n) a.val *
      modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) n) b.val) := by
  let P := modularTracialCornerProjection S n
  let T := isometricCornerLift (modularCornerInclusion (H := H) n) a.val *
    modularTracialRightAction S
      (isometricCornerLift (modularCornerInclusion (H := H) n) b.val)
  have he : P * T * P = T := by
    have h := modularTracialCornerProjection_compress S n _ _
      (modularCornerLift_mem S n a) (modularCornerLift_mem S n b)
    simpa only [modularCornerLift_left, modularCornerLift_right] using h
  have hp : P * P = P :=
    (modularTracialCornerProjection_isStarProjection S n).isIdempotentElem
  change T * P = T
  calc
    T * P = (P * T * P) * P := by rw [he]
    _ = P * T * (P * P) := by noncomm_ring
    _ = P * T * P := by rw [hp]
    _ = T := he

lemma modularCornerProduct_sum_norm (S : StandardModularData H) (n : ℕ)
    {I : Type*} [Fintype I]
    (a b : I → (modularCompressedCorner S (n + 1)).toStarSubalgebra) :
    ‖∑ i, isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) (a i).val *
      modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) (b i).val)‖ =
    ‖∑ i, gnsBundledLeft (modularCompressedTracialState S n).functional (a i) *
      gnsBundledRight (modularCompressedTracialState S n).functional
        (modularCompressedTracialState S n).tracial (b i)‖ := by
  apply gns_product_sum_norm
    (modularCompressedTracialState S n).functional
    (modularCompressedTracialState S n).tracial (modularCornerGNSInclusion S n)
    (fun a => isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val)
    (fun b => modularTracialRightAction S
      (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) b.val))
    (modularCornerGNSInclusion_left S n) (modularCornerGNSInclusion_right S n)
    (fun a b => ?_) a b
  rw [← modularCornerGNSInclusion_projection]
  exact modularCornerProduct_right_support S (n + 1) _ _

end WeakPureInfiniteness

end

end OAI
