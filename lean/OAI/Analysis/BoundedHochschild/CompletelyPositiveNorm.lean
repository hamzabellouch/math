import OAI.Analysis.BoundedHochschild.StinespringEmbedding

namespace OAI

/-! The norm bound supplied by the constructed Stinespring factorization. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringEmbedding_norm_le (φ : CompletelyPositiveMap A (H →L[ℂ] H)) :
    ‖stinespringEmbedding φ‖ ≤ Real.sqrt ‖φ 1‖ :=
  (stinespringEmbedding φ).opNorm_le_bound (Real.sqrt_nonneg _)
    (stinespringVector_bound φ)

theorem completelyPositive_norm_apply_le (φ : CompletelyPositiveMap A (H →L[ℂ] H))
    (a : A) : ‖φ a‖ ≤ ‖φ 1‖ * ‖a‖ := by
  have hV := stinespringEmbedding_norm_le φ
  calc
    ‖φ a‖ = ‖(stinespringEmbedding φ).adjoint.comp
        ((stinespringRepresentation φ a).comp (stinespringEmbedding φ))‖ :=
      congrArg norm (stinespring_factorization φ a)
    _ ≤ ‖(stinespringEmbedding φ).adjoint‖ *
        (‖stinespringRepresentation φ a‖ * ‖stinespringEmbedding φ‖) := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ Real.sqrt ‖φ 1‖ * (‖a‖ * Real.sqrt ‖φ 1‖) := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le (stinespringRepresentation φ) a
    _ = ‖φ 1‖ * ‖a‖ := by
      calc
        _ = (Real.sqrt ‖φ 1‖) ^ 2 * ‖a‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (norm_nonneg (φ 1))]

def completelyPositiveContinuous (φ : CompletelyPositiveMap A (H →L[ℂ] H)) :
    A →L[ℂ] (H →L[ℂ] H) :=
  φ.toLinearMap.mkContinuous ‖φ 1‖ (completelyPositive_norm_apply_le φ)

@[simp] lemma completelyPositiveContinuous_apply
    (φ : CompletelyPositiveMap A (H →L[ℂ] H)) (a : A) :
    completelyPositiveContinuous φ a = φ a := rfl

lemma completelyPositiveContinuous_norm_le
    (φ : CompletelyPositiveMap A (H →L[ℂ] H)) :
    ‖completelyPositiveContinuous φ‖ ≤ ‖φ 1‖ :=
  (completelyPositiveContinuous φ).opNorm_le_bound (norm_nonneg _)
    (completelyPositive_norm_apply_le φ)

end BoundedHochschild.KadisonRingrose

end

end OAI
