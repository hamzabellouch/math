import OAI.Analysis.WeakInfiniteness.ElementaryCP

namespace OAI

/-! A one-step compression after a genuine nonunital star homomorphism. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]

def innerHomCompression (φ : B →⋆ₙₐ[ℂ] D) (v : D) : B →L[ℂ] D :=
  (ContinuousLinearMap.mulLeftRight ℂ D (star v) v).comp (starHomContinuousLinear φ)

@[simp] lemma innerHomCompression_apply (φ : B →⋆ₙₐ[ℂ] D) (v : D) (b : B) :
    innerHomCompression φ v b = star v * φ b * v := rfl

lemma innerHomCompression_norm_le (φ : B →⋆ₙₐ[ℂ] D) (v : D) (hv : ‖v‖ ≤ 1) :
    ‖innerHomCompression φ v‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro b
  simp only [innerHomCompression_apply, one_mul]
  calc
    _ ≤ (‖star v‖ * ‖φ b‖) * ‖v‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖b‖) * 1 := by
      rw [norm_star]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le φ b
    _ = ‖b‖ := by ring

variable [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D]

lemma innerHomCompression_cp (φ : B →⋆ₙₐ[ℂ] D) (v : D) :
    CompletelyPositive (innerHomCompression φ v) := by
  intro n M hM
  have hp := map_nonneg (CStarMatrix.mapₙₐ φ) hM
  have he : CStarMatrix.ofMatrix (fun i j => innerHomCompression φ v (M i j)) =
      star (diagonalCopies n v) * (CStarMatrix.mapₙₐ φ M) * diagonalCopies n v := by
    ext i j
    simp [innerHomCompression_apply, diagonalCopies, CStarMatrix.mul_apply,
      CStarMatrix.star_apply, Matrix.diagonal_apply, apply_ite, ite_mul]
    rfl
  rw [he]
  exact star_left_conjugate_nonneg hp (diagonalCopies n v)

end WeakPureInfiniteness

end

end OAI
