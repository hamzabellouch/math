import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoordinatePowers

namespace OAI

/-! The joint Mellin tail with the larger neighborhood row count. -/
noncomputable section
namespace CubicFirstMoment

lemma coordinate_neighborhood_tail_power (k : ℕ) {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 =
      (2*K^2*J^2)*Y^(-10:ℝ) := by
  have hp : (Y^(1/1000:ℝ))^(1000*(2*k+7)) = Y^(2*k+7) := by
    rw [← Real.rpow_mul_natCast hY.le]
    have he : (1/1000:ℝ)*(1000*(2*k+7):ℕ) = ((2*k+7:ℕ):ℝ) := by push_cast; ring
    rw [he,Real.rpow_natCast]
  have hd : Y^(2*k)/Y^(2*k+7) = Y^(-7:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_sub hY]
    congr 1
    push_cast
    ring
  rw [hp,show K*Y^(2*k)/Y^(2*k+7) = K*(Y^(2*k)/Y^(2*k+7)) by ring,hd]
  have he : Y^4*(Y^(-7:ℝ))^2 = Y^(-10:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_natCast,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^4*(Y^(-7:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma coordinate_neighborhood_tail_le_short_tail (k : ℕ) {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^(1000*(2*k+7)))*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [coordinate_neighborhood_tail_power k (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
