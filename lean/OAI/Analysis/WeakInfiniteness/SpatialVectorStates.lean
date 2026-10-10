import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorFoundations

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal

namespace WeakPureInfiniteness

universe u v

section SpatialVectorStates

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

def spatialVectorFunctional (π : SpatialRepresentation A B) (ξ : π.space) :
    SpatialAmbient A B →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun z := inner ℂ ξ (z π ξ)
      map_add' x y := by
        change inner ℂ ξ ((x π + y π) ξ) = _
        simp only [add_apply, inner_add_right]
      map_smul' c x := by
        change inner ℂ ξ (c • (x π ξ)) = c • inner ℂ ξ (x π ξ)
        exact inner_smul_right ξ (x π ξ) c }
    (‖ξ‖ * ‖ξ‖) (by
      intro z
      calc
        ‖inner ℂ ξ (z π ξ)‖ ≤ ‖ξ‖ * ‖z π ξ‖ := norm_inner_le_norm _ _
        _ ≤ ‖ξ‖ * (‖z π‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left ((z π).le_opNorm ξ) (norm_nonneg _)
        _ ≤ ‖ξ‖ * (‖z‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero z π) (norm_nonneg _))
          (norm_nonneg _)
        _ = (‖ξ‖ * ‖ξ‖) * ‖z‖ := by ring)

lemma norm_spatialVectorFunctional_le (π : SpatialRepresentation A B) (ξ : π.space) :
    ‖spatialVectorFunctional π ξ‖ ≤ ‖ξ‖ * ‖ξ‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_self_nonneg _) _

@[simp]
lemma spatialVectorFunctional_elementary (π : SpatialRepresentation A B)
    (ξ : π.left ⊗[ℂ] π.right) (a : A) (b : B) :
    spatialVectorFunctional π (ξ : π.space) (spatialElementary a b) =
      inner ℂ ξ (TensorProduct.mapL (π.leftRep a) (π.rightRep b) ξ) := by
  change inner ℂ (ξ : Completion _) ((TensorProduct.mapL (π.leftRep a) (π.rightRep b)).completion
    (ξ : Completion _)) = _
  simp only [ContinuousLinearMap.completion_apply_coe, Completion.inner_coe]

end SpatialVectorStates

end WeakPureInfiniteness
end

end OAI
