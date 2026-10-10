import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily
import OAI.NumberTheory.CubicMoment.Estimates.PowerSavings

namespace OAI

/-! The polynomial logarithmic cost of the central integral is absorbed
by the already proved fixed power saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem log_power_powerSaving_isLittleO (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun X : ℝ => (1+Real.log X)^d*X^(5/6-δ)) =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := log_power_normalization_bound d (show 0 < δ/2 by positivity)
  apply isLittleO_of_powerSaving (show 0 < δ/2 by positivity)
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  have he : X^(-(δ/2))*X^(5/6-δ/2) = X^(5/6-δ) := by
    rw [←Real.rpow_add hXp]
    congr 1
    ring
  calc
    _ = (X^(-(δ/2))*(1+Real.log X)^d)*X^(5/6-δ/2) := by rw [←he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hbound X hX) (Real.rpow_nonneg hXp.le _)

end CubicFirstMoment

end

end OAI
