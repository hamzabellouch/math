import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelLogTail
import OAI.NumberTheory.CubicMoment.Estimates.OverlapScale

namespace OAI

/-! The logarithmic saving left after counting and integrating flat
triples is still smaller than the first-moment scale. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma fractional_log_saving_isLittleO :
    (fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^(5/4:ℝ)) =o[atTop] firstMomentScale := by
  have hL : Tendsto (fun X : ℝ => 1+Real.log X) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  have hi := tendsto_inv_atTop_zero.comp hL
  have hr := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/4)).comp hL
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub hi).mul hr
  simp only [sub_zero,mul_zero] at hh
  apply Asymptotics.isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < firstMomentScale X := div_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) (Real.log_pos hX)
    exact fun hz => (hp.ne' hz).elim
  · apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    have hp : 0 < X := zero_lt_one.trans hX
    have hl : 0 < Real.log X := Real.log_pos hX
    have hz : 0 < 1+Real.log X := by linarith
    have he : (1+Real.log X)^(5/4:ℝ) =
        (1+Real.log X)*(1+Real.log X)^(1/4:ℝ) := by
      rw [show (5/4:ℝ) = 1+1/4 by norm_num,Real.rpow_add hz,Real.rpow_one]
    unfold firstMomentScale
    simp only [Function.comp_apply]
    rw [he,Real.rpow_neg hz.le]
    field_simp [(Real.rpow_pos_of_pos hp (5/6:ℝ)).ne',hl.ne',hz.ne',
      (Real.rpow_pos_of_pos hz (1/4:ℝ)).ne']
    ring

lemma flatTriple_loglog_absorption :
    ∀ᶠ X : ℝ in atTop,
      (1+Real.log (1+Real.log X))^4 ≤ (1+Real.log X)^(1/4:ℝ) := by
  have hL : Tendsto (fun X : ℝ => 1+Real.log X) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_log_atTop
  filter_upwards [hL.eventually (overlap_power_log_saving (by norm_num : (0:ℝ) < 1/4) 4 0),
    Real.tendsto_log_atTop.eventually_ge_atTop 0] with X hh hx
  apply (div_le_one (Real.rpow_pos_of_pos (by linarith) _)).mp
  simpa only [Nat.mul_zero,pow_zero,div_one] using hh

lemma flatTriple_counted_scale_isLittleO :
    (fun X : ℝ => X^(5/6:ℝ)*(1+Real.log (1+Real.log X))^4/
      (1+Real.log X)^(3/2:ℝ)) =o[atTop] firstMomentScale := by
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun X : ℝ =>
    X^(5/6:ℝ)/(1+Real.log X)^(5/4:ℝ)) ?_ fractional_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [flatTriple_loglog_absorption,eventually_ge_atTop (1:ℝ)] with X hh hX
  have hp : 0 < X := zero_lt_one.trans_le hX
  have hz : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hq : 0 ≤ 1+Real.log (1+Real.log X) := by
    have hlog := Real.log_nonneg (show 1 ≤ 1+Real.log X by linarith [Real.log_nonneg hX])
    linarith
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),one_mul]
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by positivity)) (by positivity)).trans_eq
  have he : (1+Real.log X)^(3/2:ℝ) =
      (1+Real.log X)^(1/4:ℝ)*(1+Real.log X)^(5/4:ℝ) := by
    rw [← Real.rpow_add hz]
    norm_num
  rw [he]
  field_simp

end CubicFirstMoment

end

end OAI
