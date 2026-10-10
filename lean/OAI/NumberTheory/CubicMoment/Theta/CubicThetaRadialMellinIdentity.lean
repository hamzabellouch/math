import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialMellinIntegrability

namespace OAI

/-! The radial observation factor is an entire Mellin transform of one
fixed rapidly decaying kernel. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaFourierRadialTest_dilated (h : Eisenstein) (W : C_c(ℝ,ℂ)) (s : ℂ) :
    cubicThetaFourierRadialTest h W s=
      ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^2*
        (∫ u in Ioi (0:ℝ), (u:ℂ)^(s-2)*cubicThetaLinearHeat v (cubicThetaRowHeatScale h) u) := by
  unfold cubicThetaFourierRadialTest
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  change 2<v at hv
  dsimp only
  have hv0 : 0<v := by linarith [hv]
  have hd := cubicThetaHeat_height_dilation hv0 (cubicThetaRowHeatScale h) s
  calc
    _ = star (W v)/(v:ℂ)^3*((v:ℂ)^s*
      (∫ t in Ioi (0:ℝ), cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t)) := by ring
    _ = _ := by
      rw [hd]
      field_simp [Complex.ofReal_ne_zero.mpr hv0.ne']

theorem cubicThetaFourierRadialTest_mellin {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) (s : ℂ) :
    cubicThetaFourierRadialTest h W s=
      mellin (cubicThetaAveragedHeat W (cubicThetaRowHeatScale h)) (s-1) := by
  rw [cubicThetaFourierRadialTest_dilated]
  have hi := cubicThetaRadialMellin_integrable W (cubicThetaRowHeatScale_pos hh) s
  calc
    _ = ∫ v in Ioi (2:ℝ), ∫ u in Ioi (0:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      unfold cubicThetaRadialMellinIntegrand
      ring
    _ = ∫ u in Ioi (0:ℝ), ∫ v in Ioi (2:ℝ),
        cubicThetaRadialMellinIntegrand W (cubicThetaRowHeatScale h) s (v,u) :=
      integral_integral_swap hi
    _ = _ := by
      unfold mellin
      apply integral_congr_ae
      filter_upwards with u
      simp only [show s-1-1=s-2 by ring,smul_eq_mul,cubicThetaAveragedHeat]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      unfold cubicThetaRadialMellinIntegrand
      ring

theorem cubicThetaFourierRadialTest_entire {h : Eisenstein} (hh : h≠0)
    (W : C_c(ℝ,ℂ)) : Differentiable ℂ (cubicThetaFourierRadialTest h W) := by
  have he : cubicThetaFourierRadialTest h W=
      (fun s : ℂ => mellin (cubicThetaAveragedHeat W (cubicThetaRowHeatScale h)) (s-1)) :=
    funext (cubicThetaFourierRadialTest_mellin hh W)
  rw [he]
  exact (cubicThetaAveragedHeat_mellin_entire W (cubicThetaRowHeatScale_pos hh)).comp
    (differentiable_id.sub_const 1)

end CubicFirstMoment

end

end OAI
