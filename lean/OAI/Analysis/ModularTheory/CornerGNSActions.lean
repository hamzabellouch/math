import OAI.Analysis.ModularTheory.CornerGNSRange
import OAI.Analysis.ModularTheory.CornerRightVectors
import OAI.Analysis.OperatorAlgebra.GNSHomIntertwining

namespace OAI

/-! Both actual corner actions intertwine with the finite tracial GNS actions. -/
noncomputable section
open MeasureTheory
open scoped ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local irreducible] modularCompressedTracialState

lemma modularCornerGNSInclusion_left (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S (n + 1)).toStarSubalgebra)
    (x : gnsHilbert (modularCompressedTracialState S n).functional) :
    isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val
        (modularCornerGNSInclusion S n x) =
      modularCornerGNSInclusion S n
        (gnsBundledLeft (modularCompressedTracialState S n).functional a x) := by
  let ψ := (isometricCornerLiftHom (modularCornerInclusion (H := H) (n + 1))).comp
    (modularCompressedCorner S (n + 1)).toStarSubalgebra.subtype.toNonUnitalStarAlgHom
  exact gnsBundledLeft_intertwines_hom (modularCompressedTracialState S n).functional
    (modularCornerGNSInclusion S n) (((‖modularCoreWeightVector S (n + 1)‖⁻¹ : ℝ) : ℂ))
    ψ (modularCoreWeightVector S (n + 1)) (modularCornerGNSInclusion_vector S n) a x

lemma modularCornerGNSInclusion_right (S : StandardModularData H) (n : ℕ)
    (b : (modularCompressedCorner S (n + 1)).toStarSubalgebra)
    (x : gnsHilbert (modularCompressedTracialState S n).functional) :
    modularTracialRightAction S
      (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) b.val)
        (modularCornerGNSInclusion S n x) =
      modularCornerGNSInclusion S n
        (gnsBundledRight (modularCompressedTracialState S n).functional
          (modularCompressedTracialState S n).tracial b x) :=
  gnsBundledRight_intertwines (modularCompressedTracialState S n).functional
    (modularCompressedTracialState S n).tracial (modularCornerGNSInclusion S n)
    (((‖modularCoreWeightVector S (n + 1)‖⁻¹ : ℝ) : ℂ))
    (fun a => isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val
      (modularCoreWeightVector S (n + 1)))
    (modularCornerGNSInclusion_vector S n) b
    (modularTracialRightAction S
      (isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) b.val))
    (fun a => modularTracialRightAction_lift_vector S (n + 1) a b) x

end WeakPureInfiniteness

end

end OAI
