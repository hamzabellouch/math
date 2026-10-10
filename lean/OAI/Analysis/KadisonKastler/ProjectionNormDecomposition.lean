import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

/-! # Squared-norm decompositions for nested projections -/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_apply_norm_le {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using P.le_of_opNorm_le (hP.norm_le P) x

theorem projection_complement_inner {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    inner ℂ (P x) ((1 - P) x) = 0 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  rw [← P.adjoint_inner_right, hs]
  change inner ℂ x ((P * (1 - P)) x) = 0
  rw [hz, zero_apply, inner_zero_right]

theorem projection_norm_sq_decomposition {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := by
  calc
    _ = ‖P x + (1 - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
          (projection_complement_inner hP x)).symm
    _ = ‖x‖ ^ 2 := by simp

theorem nested_projection_reverse {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hPR : P * R = P) :
    R * P = P := by
  have h := congrArg star hPR
  simpa only [star_mul, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq] using h

theorem nested_projection_norm_sq_eq {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hPR : P * R = P) (x : H) :
    ‖P x‖ ^ 2 + ‖(R - P) x‖ ^ 2 = ‖R x‖ ^ 2 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (R - P) = 0 := by
    rw [mul_sub, hPR, hP.isIdempotentElem.eq, sub_self]
  have hi : inner ℂ (P x) ((R - P) x) = 0 := by
    rw [← P.adjoint_inner_right, hs]
    change inner ℂ x ((P * (R - P)) x) = 0
    rw [hz, zero_apply, inner_zero_right]
  calc
    _ = ‖P x + (R - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi).symm
    _ = ‖R x‖ ^ 2 := by simp

theorem nested_projection_norm_sq {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hPR : P * R = P) (x : H) :
    ‖P x‖ ^ 2 + ‖(R - P) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [nested_projection_norm_sq_eq hP hPR]
  calc
    _ ≤ ‖x‖ ^ 2 := by gcongr; exact projection_apply_norm_le hR x

end

end KadisonKastler

end OAI
