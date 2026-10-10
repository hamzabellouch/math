import OAI.NumberTheory.DirichletL.PrincipalSlotEstimate

namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal
theorem compensated_phase_error_bound (V W D P B q vInv : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hv : ‖vInv‖≤1) (hBD : B * D = vInv) (hWq : vInv*W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P*vInv‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖vInv - q‖ ≤ 2 := by
    have := norm_sub_le vInv q
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(vInv - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖vInv - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + vInv - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + vInv - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (vInv - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖vInv - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + vInv - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD hWq
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(vInv - q) * (V / (1 - V) - D)‖ + ‖(B + vInv - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

end SevenEighths.ProbeLocal
end

end OAI
