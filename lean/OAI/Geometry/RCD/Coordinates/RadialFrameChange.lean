import OAI.Geometry.RCD.Coordinates.MatrixNormConversion

namespace OAI

/-! # Transporting a radial coefficient operator to the common frame -/

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded change of frame preserves smallness of a radial operator's
error from the identity, with the explicit two frame factors. -/
theorem radial_frame_change_bound (P : E ≃L[ℝ] E) (A : E →L[ℝ] E) :
    ‖P.symm.toContinuousLinearMap * A * P.toContinuousLinearMap - 1‖ ≤
      ‖P.symm.toContinuousLinearMap‖ * ‖A - 1‖ * ‖P.toContinuousLinearMap‖ := by
  have hid : P.symm.toContinuousLinearMap * A * P.toContinuousLinearMap - 1 =
      P.symm.toContinuousLinearMap * (A - 1) * P.toContinuousLinearMap := by
    ext x
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self,
      ContinuousLinearEquiv.coe_coe, map_sub,
      ContinuousLinearEquiv.symm_apply_apply]
  rw [hid]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))

end RegularPointCoordinates

end

end OAI
