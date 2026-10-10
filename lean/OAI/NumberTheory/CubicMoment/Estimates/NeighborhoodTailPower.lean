import OAI.NumberTheory.CubicMoment.Estimates.MellinMomentPowers

namespace OAI

/-! A thirtieth Mellin moment handles the larger row count uniformly across
both exceptional conductor neighborhoods. -/
noncomputable section
namespace CubicFirstMoment

lemma neighborhood_mellin_tail_power {Y K J : ℝ} (hY : 0 < Y) :
    2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 =
      (2*K^2*J^2)*Y^(-68/5:ℝ) := by
  have hp : (Y^(9/25:ℝ))^30 = Y^(54/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le]
    norm_num
  have hd : Y^2/Y^(54/5:ℝ) = Y^(-44/5:ℝ) := by
    rw [← Real.rpow_two,← Real.rpow_sub hY]
    norm_num
  rw [hp,show K*Y^2/Y^(54/5:ℝ) = K*(Y^2/Y^(54/5:ℝ)) by ring,hd]
  have he : Y^4*(Y^(-44/5:ℝ))^2 = Y^(-68/5:ℝ) := by
    rw [← Real.rpow_mul_natCast hY.le,← Real.rpow_natCast,← Real.rpow_add hY]
    norm_num
  calc
    _ = (2*K^2*J^2)*(Y^4*(Y^(-44/5:ℝ))^2) := by ring
    _ = _ := by rw [he]

lemma neighborhood_mellin_tail_le {Y K J : ℝ} (hY : 1 ≤ Y) :
    2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 ≤
      (2*K^2*J^2)*Y^(-42/5:ℝ) := by
  rw [neighborhood_mellin_tail_power (zero_lt_one.trans_le hY)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
