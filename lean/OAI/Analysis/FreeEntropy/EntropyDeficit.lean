import OAI.Analysis.FreeEntropy.RealTail

namespace OAI

noncomputable section
open MeasureTheory Set Filter Finset
namespace FiniteEntropySeparation.Model
variable (p : ℕ) [NeZero p]
theorem cumulantConstant_pos : 0 < cumulantConstant p := by
  unfold cumulantConstant
  exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos p))))
theorem fisherDeficit_tail_integrable (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fisherDeficit p) (Ioi a) :=
  (integrableOn_Ioi_translate a).mp (fisherDeficit_shift_integrable p hp a ha)
theorem fisherDeficit_tail_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ ∫ u in Ioi a, fisherDeficit p u := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact fisherDeficit_nonneg p u (lt_trans ha hu)
theorem fisherDeficit_tail_le (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (hKa : 2*(cumulantConstant p)^2 ≤ a) :
    (∫ u in Ioi a, fisherDeficit p u) ≤ 2*(cumulantConstant p)^6/(3*a^3) := by
  have hi := (inverseFourth_integrable ha).const_mul (2*(cumulantConstant p)^6)
  have hle : (∫ u in Ioi a, fisherDeficit p u) ≤
      ∫ u in Ioi a, 2*(cumulantConstant p)^6 * (1/u^4) := by
    apply integral_mono_ae (fisherDeficit_tail_integrable p hp a ha) hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simpa only [mul_one_div] using
      (fisherDeficit_bounds p hp u (lt_trans ha hu) (hKa.trans hu.le)).2
  rw [integral_const_mul, inverseFourth_integral ha] at hle
  simpa only [mul_one_div] using hle
theorem chiStar_tail_formula (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) :
    chiStar (τ p) (X p a) (auxiliaryNoise p) =
      ((gaussianEntropy p a - (1/2 : ℝ) * ∫ u in Ioi a, fisherDeficit p u : ℝ) : EReal) := by
  rw [chiStar_covariance_formula p hp a ha, integral_Ioi_translate]
theorem entropy_deficit_le (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (hKa : 2*(cumulantConstant p)^2 ≤ a) :
    (1/2 : ℝ) * (∫ u in Ioi a, fisherDeficit p u) ≤ 1/24 := by
  have hK := cumulantConstant_pos p
  have hb := fisherDeficit_tail_le p hp a ha hKa
  have hc : (2*(cumulantConstant p)^2)^3 ≤ a^3 := pow_le_pow_left₀ (by positivity) hKa 3
  have hd : 0 < 3*a^3 := by positivity
  have he : 2*(cumulantConstant p)^6/(3*a^3) ≤ 1/12 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [hc]
  linarith
end FiniteEntropySeparation.Model

end

end OAI
