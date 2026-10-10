import OAI.Probability.ContinuumTransition.PackingLimit

namespace OAI

section
open scoped Topology BigOperators
open Filter MeasureTheory Set
namespace ContinuumTemperature

lemma coreProfile_stable_zero (t : ℝ) (n : ℕ) (x : Fin n → Space) :
    ((-(0 : ℝ)*n : ℝ) : EReal) ≤ energy (coreProfile t) x := by
  apply le_trans _ (coe_pairSum_le_energy _ x)
  apply EReal.coe_le_coe_iff.mpr
  simp only [neg_zero,zero_mul]
  unfold pairSum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact coreProfile_nonneg _ _

lemma core_log_upper {t : ℝ} (ht : 2*(1+shellDelta)*Real.exp (-t) < 1)
    (d L : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    Real.log (grandIntegral (gibbsFamily (fun x y => coreProfile t ‖x-y‖) β d) (cube L)) ≤
      volume.real (cube L)*(1+Real.exp (d-β*t^2/2))+
        (packingNumber L : ℝ)*(2+Real.log (max 1 (clusterActivity t d))) := by
  have hfin := core_gibbs_finite t d hβ (isCompact_cube L).measure_lt_top.ne
  have hz := grandIntegral_gibbs_pos _ β d (cube L) hfin.summable
  have hh := Real.log_le_log hz (core_grand_upper ht d L hβ)
  have hM : 0 < (packingNumber L : ℝ)+1 := by positivity
  have hθ : 0 < max 1 (clusterActivity t d) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hM).ne' (pow_pos hθ _).ne',
    Real.log_mul (Real.exp_pos _).ne' hM.ne',Real.log_exp,Real.log_pow] at hh
  have hl := Real.log_le_sub_one_of_pos hM
  linarith only [hh,hl]

theorem core_pressure_upper {t β : ℝ} (ht : 1 < t) (hβ : 0 ≤ β)
    (hsep : 2*(1+shellDelta)*Real.exp (-t) < 1) (h : ℝ) :
    physicalPressure (coreProfile t) t (β,h) ≤
      (1+Real.exp (t*h-β*t^2/2)+packingDensity*(2+Real.log (max 1 (clusterActivity t (t*h)))))/t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hlim := physicalPressure_tendsto
    (measurable_radialPotential (measurable_coreProfile t)) ht hβ
    (coreProfile_stable_zero t) (fun _ _ => le_refl _) (h := h)
  have hl := (((packingNumber_tendsto.mul_const
    (2+Real.log (max 1 (clusterActivity t (t*h))))).const_add
      (1+Real.exp (t*h-β*t^2/2))).div_const t)
  apply le_of_tendsto_of_tendsto hlim hl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hh := div_le_div_of_nonneg_right (core_log_upper hsep (t*h) L hβ)
    (show 0 ≤ t*L^3 by positivity)
  rw [grandIntegral_radial,Measure.real,volume_cube,ENNReal.toReal_pow,ENNReal.toReal_ofReal hL.le] at hh
  convert hh using 1; field_simp

lemma log_max_one {x : ℝ} (hx : 0 < x) : Real.log (max 1 x) = max 0 (Real.log x) := by
  by_cases h : 1 ≤ x
  · rw [max_eq_right h,max_eq_right (Real.log_nonneg h)]
  · have h' := le_of_not_ge h
    rw [max_eq_left h',Real.log_one,max_eq_left (Real.log_nonpos hx.le h')]

lemma volume_shellBall (t : ℝ) :
    volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))) =
      ((1+shellDelta)^3*volume.real (Metric.ball (0 : Space) 1))*Real.exp (-3*t) := by
  rw [Measure.addHaar_real_closedBall volume _ (by unfold shellDelta; positivity)]
  have hd : Module.finrank ℝ Space = 3 := by simp [Space]
  rw [hd,mul_pow,← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show (3 : ℝ)*(-t) = -3*t by ring]
  ring

noncomputable def shellVolumeConstant : ℝ :=
  (1+shellDelta)^3*volume.real (Metric.ball (0 : Space) 1)

lemma shellVolumeConstant_pos : 0 < shellVolumeConstant := by
  unfold shellVolumeConstant
  apply mul_pos (by unfold shellDelta; positivity)
  exact ENNReal.toReal_pos (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr zero_lt_one)).ne' measure_ball_lt_top.ne

lemma log_clusterActivity (t d : ℝ) :
    Real.log (max 1 (clusterActivity t d)) =
      max 0 (d+3*max 0 (Real.log shellVolumeConstant-3*t+d)) := by
  have hw : 0 < volume.real (Metric.closedBall (0 : Space) ((1+shellDelta)*Real.exp (-t))) := by
    rw [volume_shellBall]
    exact mul_pos shellVolumeConstant_pos (Real.exp_pos _)
  have hθ : 0 < clusterActivity t d := by
    unfold clusterActivity
    exact mul_pos (Real.exp_pos _) (pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) 3)
  rw [log_max_one hθ]
  congr 1
  unfold clusterActivity
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))),
    Real.log_exp,Real.log_pow,log_max_one (mul_pos hw (Real.exp_pos _)),
    Real.log_mul hw.ne' (Real.exp_pos _).ne',Real.log_exp,volume_shellBall]
  change d+(3 : ℝ)*max 0 (Real.log (shellVolumeConstant*Real.exp (-3*t))+d) = _
  rw [Real.log_mul shellVolumeConstant_pos.ne' (Real.exp_pos _).ne',Real.log_exp]
  ring_nf

end ContinuumTemperature
end

end OAI
