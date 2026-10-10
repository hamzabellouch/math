import Mathlib
import OAI.Geometry.CAT0Fillings.Model

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma sphereArea_two : sphereArea 2 = 4*Real.pi := by
  change (2+1:ℝ) * (volume (Metric.ball (0 : Euc 3) 1)).toReal = _
  rw [EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity)]
  ring
lemma fillingCoefficient_two : fillingCoefficient 2 = 1/(6*Real.sqrt Real.pi) := by
  rw [fillingCoefficient,sphereArea_two]
  norm_num only [Nat.cast_ofNat,Nat.reduceAdd]
  rw [←Real.sqrt_eq_rpow,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num
  ring
lemma fillingCoefficient_two_pos : 0 < fillingCoefficient 2 := by
  rw [fillingCoefficient_two]
  positivity
lemma fillingCoefficient_two_sq : 36*Real.pi*(fillingCoefficient 2)^2 = 1 := by
  rw [fillingCoefficient_two,div_pow,one_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le]
  field_simp [Real.pi_ne_zero]
  ring
lemma fillingPower_two : fillingPower 2 = (3:ℝ)/2 := by norm_num [fillingPower]
end CAT0Fillings
end

end OAI
