import OAI.Analysis.ModularTheory.CornerVectors

namespace OAI

/-! Right multiplication on the concrete vectors of a finite modular corner. -/
noncomputable section
open MeasureTheory
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularTracialRightAction_lift_vector (S : StandardModularData H) (n : ℕ)
    (a b : (modularCompressedCorner S n).toStarSubalgebra) :
    modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) n) b.val)
      (isometricCornerLift (modularCornerInclusion (H := H) n) a.val
        (modularCoreWeightVector S n)) =
      isometricCornerLift (modularCornerInclusion (H := H) n) (a * b).val
        (modularCoreWeightVector S n) := by
  let T := modularFiniteWeightCut S
    (isometricCornerLift (modularCornerInclusion (H := H) n) a.val)
    (modularCornerLift_mem S n a) n
  have hT : T.val = isometricCornerLift (modularCornerInclusion (H := H) n) a.val :=
    modularCornerLift_right n a.val
  have hv : modularFiniteWeightMap S T =
      isometricCornerLift (modularCornerInclusion (H := H) n) a.val
        (modularCoreWeightVector S n) :=
    modularFiniteWeightMap_cut S _ (modularCornerLift_mem S n a) n
  let R := modularFiniteWeightRight S T
    (isometricCornerLift (modularCornerInclusion (H := H) n) b.val)
    (modularCornerLift_mem S n b)
  have hR : R.val * modularFiniteProjection (H := H) n = R.val := by
    change (T.val * isometricCornerLift (modularCornerInclusion (H := H) n) b.val) *
      modularFiniteProjection (H := H) n = _
    rw [mul_assoc, modularCornerLift_right]
    rfl
  calc
    _ = modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) n) b.val)
        (modularFiniteWeightMap S T) := congrArg
      (modularTracialRightAction S
        (isometricCornerLift (modularCornerInclusion (H := H) n) b.val)) hv.symm
    _ = modularFiniteWeightMap S R :=
      modularTracialRightAction_vector S T _ (modularCornerLift_mem S n b)
    _ = R.val (modularCoreWeightVector S n) :=
      modularFiniteWeight_supported_vector S n R hR
    _ = (isometricCornerLift (modularCornerInclusion (H := H) n) a.val *
        isometricCornerLift (modularCornerInclusion (H := H) n) b.val)
        (modularCoreWeightVector S n) := by
      change (T.val * isometricCornerLift (modularCornerInclusion (H := H) n) b.val)
        (modularCoreWeightVector S n) = _
      rw [hT]
    _ = _ := congrArg
      (fun U : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) =>
        U (modularCoreWeightVector S n))
      (isometricCornerLift_mul (modularCornerInclusion (H := H) n) a.val b.val).symm

end WeakPureInfiniteness

end

end OAI
