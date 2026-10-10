import OAI.Geometry.RCD.Harmonic.TwoCenterCommutator

namespace OAI

/-! # Recovering the difference of radial operators in covector order -/

noncomputable section
namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine Sobolev identity acts on covectors, so its commutator has
this reversed order. The same near-identity absorption controls B. -/
theorem covector_commutator_norm_le (A B : E →L[ℝ] E)
    (hA : ‖A - 1‖ ≤ 1 / 4) {η : ℝ}
    (herror : ‖A * B - B * (A - 1)‖ ≤ η) : ‖B‖ ≤ 2 * η := by
  have hid : B = (A * B - B * (A - 1)) -
      ((A - 1) * B - B * (A - 1)) := by noncomm_ring
  have ht : ‖B‖ ≤ ‖A * B - B * (A - 1)‖ +
      (‖A - 1‖ * ‖B‖ + ‖B‖ * ‖A - 1‖) := by
    calc
      ‖B‖ = ‖(A * B - B * (A - 1)) - ((A - 1) * B - B * (A - 1))‖ := congrArg norm hid
      _ ≤ ‖A * B - B * (A - 1)‖ + ‖(A - 1) * B - B * (A - 1)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl ((norm_sub_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)))
  have hs := mul_le_mul_of_nonneg_left hA (norm_nonneg B)
  nlinarith

end RegularPointCoordinates

end

end OAI
