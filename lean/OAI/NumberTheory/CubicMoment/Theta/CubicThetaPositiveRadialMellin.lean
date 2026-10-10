import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveAveragedHeat

namespace OAI

/-! The full positive-height radial Fourier factor is entire. All
integral interchanges retain the positive cutoff rather than discarding it. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaPositiveRadialMellin_integrable (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) (s : ℂ) :
    Integrable (cubicThetaRadialMellinIntegrand W A s)
      ((volume.restrict (Ioi ε)).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hh := (cubicThetaDoubleHeat_mellinConvergent (Real.sqrt_pos.mpr hε)
    (mul_pos hA hε) (s-1)).norm
  change IntegrableOn (fun u : ℝ => ‖(u:ℂ)^(s-1-1)*
    cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖) (Ioi 0) at hh
  rw [show s-1-1=s-2 by ring] at hh
  have hm := (cubicThetaPositiveRadialWeight_integrable W hε).mul_prod hh
  rw [Measure.prod_restrict] at hm ⊢
  apply hm.mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaRadialMellinIntegrand cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  have hb := mul_le_mul_of_nonneg_left
    (cubicThetaPositiveLinearHeat_bound W hε hA hp.2 hp.1) (_root_.norm_nonneg ((p.2:ℂ)^(s-2)))
  simpa only [cubicThetaRadialMellinIntegrand,norm_mul,mul_comm,mul_left_comm,mul_assoc] using hb

lemma cubicThetaPositiveRadialTest_dilated (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    cubicThetaPositiveRadialTest h W ε s=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^2*
        (∫ u in Ioi (0:ℝ),(u:ℂ)^(s-2)*cubicThetaLinearHeat v (cubicThetaRowHeatScale h) u) := by
  unfold cubicThetaPositiveRadialTest
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have hv0 : 0<v := hε.trans hv
  have hd := cubicThetaHeat_height_dilation hv0 (cubicThetaRowHeatScale h) s
  calc
    _ = star (W v)/(v:ℂ)^3*((v:ℂ)^s*
      (∫ t in Ioi (0:ℝ),cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)) := by ring
    _ = _ := by
      rw [hd]
      field_simp [Complex.ofReal_ne_zero.mpr hv0.ne']

theorem cubicThetaPositiveRadialTest_mellin {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) (s : ℂ) :
    cubicThetaPositiveRadialTest h W ε s=
      mellin (cubicThetaPositiveAveragedHeat W ε (cubicThetaRowHeatScale h)) (s-1) := by
  rw [cubicThetaPositiveRadialTest_dilated h W hε]
  have hi := cubicThetaPositiveRadialMellin_integrable W hε (cubicThetaRowHeatScale_pos hh) s
  calc
    _ = ∫ v in Ioi ε,∫ u in Ioi (0:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      unfold cubicThetaRadialMellinIntegrand
      ring
    _ = ∫ u in Ioi (0:ℝ),∫ v in Ioi ε,
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) :=
      integral_integral_swap hi
    _ = _ := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards with u
      simp only [show s-1-1=s-2 by ring,smul_eq_mul,cubicThetaPositiveAveragedHeat]
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      unfold cubicThetaRadialMellinIntegrand
      ring

theorem cubicThetaPositiveRadialTest_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) :
    Differentiable ℂ (cubicThetaPositiveRadialTest h W ε) := by
  have he : cubicThetaPositiveRadialTest h W ε=
      (fun s : ℂ => mellin (cubicThetaPositiveAveragedHeat W ε (cubicThetaRowHeatScale h)) (s-1)) :=
    funext (cubicThetaPositiveRadialTest_mellin hh W hε)
  rw [he]
  exact (cubicThetaPositiveAveragedHeat_mellin_entire W hε (cubicThetaRowHeatScale_pos hh)).comp
    (differentiable_id.sub_const 1)

end CubicFirstMoment

end

end OAI
