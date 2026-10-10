import OAI.NumberTheory.JointDickman.Amplification.RampProfile

namespace OAI

/-! # Lipschitz control of normalized cell integrals -/

namespace JointDickman

open MeasureTheory
open scoped NNReal

theorem cellAverage_profile_error {f : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L f)
    {a b : ℝ} (hab : a < b) (t : ℝ) :
    |(∫ x in a..b, f (x - t)) / (b - a) - f (a - t)| ≤ L * (b - a) := by
  have hint : IntervalIntegrable (fun x => f (x - t)) volume a b :=
    (hLip.continuous.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have heq : (∫ x in a..b, f (x - t)) / (b - a) - f (a - t) =
      (∫ x in a..b, f (x - t) - f (a - t)) / (b - a) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [(sub_pos.mpr hab).ne']
  rw [heq, abs_div, abs_of_pos (sub_pos.mpr hab)]
  apply (div_le_iff₀ (sub_pos.mpr hab)).mpr
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun x => f (x - t) - f (a - t))
    (C := (L : ℝ) * (b - a)) (fun x hx => by
      rw [Set.uIoc_of_le hab.le] at hx
      rcases hx with ⟨hxa, hxb⟩
      have hh := hLip.dist_le_mul (x - t) (a - t)
      rw [Real.dist_eq, Real.dist_eq, sub_sub_sub_cancel_right, abs_of_nonneg (by linarith : 0 ≤ x - a)] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith : x - a ≤ b - a) L.coe_nonneg))
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hab)] using h

/-- Normalize the probability error by the actual cell mass, then add
only the Lipschitz oscillation across that cell. -/
theorem normalizedCell_profile_error {f : ℝ → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L f)
    {a b P φ ε : ℝ} (hab : a < b) (hφ : 0 < φ) (t : ℝ)
    (hlocal : |P - (∫ x in a..b, f (x - t)) / φ| ≤ ε) :
    |P / ((b - a) / φ) - f (a - t)| ≤ ε / ((b - a) / φ) + L * (b - a) := by
  have hm : 0 < (b - a) / φ := div_pos (sub_pos.mpr hab) hφ
  have heq : P / ((b - a) / φ) - f (a - t) =
      (P - (∫ x in a..b, f (x - t)) / φ) / ((b - a) / φ) +
      ((∫ x in a..b, f (x - t)) / (b - a) - f (a - t)) := by
    field_simp [hφ.ne', (sub_pos.mpr hab).ne']
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_div, abs_of_pos hm]
    exact div_le_div_of_nonneg_right hlocal hm.le
  · exact cellAverage_profile_error hLip hab t

end JointDickman

end OAI
