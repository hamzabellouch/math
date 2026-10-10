import OAI.Analysis.WeakInfiniteness.NuclearTensorMap
import OAI.Analysis.WeakInfiniteness.TensorFlipEquivalence

namespace OAI

/-! Right-leg completely positive tensor maps, obtained by the actual tensor flip. -/
noncomputable section
namespace WeakPureInfiniteness

variable {A B C : Type*} [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]

def minimalRightCPMap (φ : B →L[ℂ] C) : MinimalTensor A B →L[ℂ] MinimalTensor A C :=
  (starHomContinuousLinear (minimalFlipHom C A)).comp
    ((minimalCPMap φ).comp (starHomContinuousLinear (minimalFlipHom A B)))

lemma minimalRightCPMap_elementary (φ : B →L[ℂ] C) (hφ : CompletelyPositive φ)
    (a : A) (b : B) :
    minimalRightCPMap φ (minimalElementary a b) = minimalElementary a (φ b) := by
  change minimalFlipHom C A
    (minimalCPMap φ (minimalFlipHom A B (minimalElementary a b))) = _
  rw [minimalFlipHom_elementary, minimalCPMap_elementary φ hφ, minimalFlipHom_elementary]

lemma minimalRightCPMap_norm_le (φ : B →L[ℂ] C) (hφ : CompletelyPositive φ)
    (z : MinimalTensor A B) :
    ‖minimalRightCPMap φ z‖ ≤ (4 * ‖φ‖) * ‖z‖ := by
  change ‖minimalFlipHom C A (minimalCPMap φ (minimalFlipHom A B z))‖ ≤ _
  calc
    _ ≤ ‖minimalCPMap φ (minimalFlipHom A B z)‖ :=
      NonUnitalStarAlgHom.norm_apply_le _ _
    _ ≤ (4 * ‖φ‖) * ‖minimalFlipHom A B z‖ := norm_minimalCPMap_le φ hφ _
    _ ≤ (4 * ‖φ‖) * ‖z‖ := mul_le_mul_of_nonneg_left
      (NonUnitalStarAlgHom.norm_apply_le _ _) (mul_nonneg (by norm_num) (norm_nonneg _))

end WeakPureInfiniteness

end

end OAI
