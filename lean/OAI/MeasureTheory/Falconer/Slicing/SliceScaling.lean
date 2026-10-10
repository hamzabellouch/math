import OAI.MeasureTheory.Falconer.Slicing.OrientedSlice

namespace OAI

/-! # The fixed spatial rescaling of a selected planar slice -/

namespace Falconer
open NormedSpace
variable {m : ℕ}

theorem slice_scaled_distance {L : ℝ} (hL : 0 < L) (x c : Space m) :
    dist (L⁻¹ • x) c = L⁻¹*dist x (L • c) := by
  have he : L⁻¹ • x-c = L⁻¹ • (x-L • c) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hL.ne',one_smul]
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hL),dist_eq_norm]

theorem slice_scaled_tube_width {L ε : ℝ} (hL : 0 < L) (w x a : Space m)
    (htube : ‖perpendicularPart w (x-a)‖ ≤ ε) :
    ‖perpendicularPart w (L⁻¹ • x-L⁻¹ • a)‖ ≤ L⁻¹*ε := by
  rw [← smul_sub,perpendicularPart_smul,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hL)]
  exact mul_le_mul_of_nonneg_left htube (inv_nonneg.mpr hL.le)

end Falconer

end OAI
