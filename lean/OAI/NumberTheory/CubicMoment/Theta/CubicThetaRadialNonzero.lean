import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialTent

namespace OAI

/-! The fixed radial test is nontrivial: its value at s=2 is strictly
positive. This supplies a genuine analytic denominator for continuation. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialTest_kernel_real (A u v : ℝ) :
    star (cubicThetaRadialTestWeight v)/(v:ℂ)^2*cubicThetaLinearHeat v A u=
      ((cubicThetaRadialTent v/v^2*Real.exp (-v*u-A*v/u):ℝ):ℂ) := by
  rw [cubicThetaRadialTestWeight_apply,cubicThetaLinearHeat]
  push_cast
  simp

lemma cubicThetaAveragedHeat_test_re_pos {A u : ℝ} (hA : 0<A) (hu : 0<u) :
    0<(cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re := by
  let f := fun v : ℝ => cubicThetaRadialTent v/v^2*Real.exp (-v*u-A*v/u)
  have hi : IntegrableOn f (Ioi (2:ℝ)) := by
    have hr := (cubicThetaAveragedHeat_integrable cubicThetaRadialTestWeight hA hu).re
    change IntegrableOn (fun v : ℝ =>
      (star (cubicThetaRadialTestWeight v)/(v:ℂ)^2*cubicThetaLinearHeat v A u).re) (Ioi 2) at hr
    simpa only [cubicThetaRadialTest_kernel_real,Complex.ofReal_re] using hr
  have hc : ContinuousOn f (Ioi (2:ℝ)) := by
    apply ContinuousOn.mul
    · exact cubicThetaRadialTent_continuous.continuousOn.div (continuousOn_id.pow 2)
        (fun v hv => pow_ne_zero _ (ne_of_gt (lt_trans (by norm_num) hv)))
    · exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
  have hp : 0<∫ v in Ioi (2:ℝ), f v :=
    cubicThetaPositive_setIntegral hc hi
      (fun v _ => mul_nonneg (div_nonneg (cubicThetaRadialTent_nonneg v) (sq_nonneg v))
        (Real.exp_nonneg _)) (x:=3) (by norm_num)
      (by dsimp [f,cubicThetaRadialTent]; positivity)
  have hr := integral_re (cubicThetaAveragedHeat_integrable cubicThetaRadialTestWeight hA hu)
  change (∫ v in Ioi (2:ℝ),
    (star (cubicThetaRadialTestWeight v)/(v:ℂ)^2*cubicThetaLinearHeat v A u).re)=
      (cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re at hr
  rw [← hr]
  simpa only [cubicThetaRadialTest_kernel_real,Complex.ofReal_re] using hp

theorem cubicThetaFourierRadialTest_nonzero {h : Eisenstein} (hh : h≠0) :
    cubicThetaFourierRadialTest h cubicThetaRadialTestWeight 2≠0 := by
  let A := cubicThetaRowHeatScale h
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  have hi : IntegrableOn (cubicThetaAveragedHeat cubicThetaRadialTestWeight A) (Ioi (0:ℝ)) := by
    have hm := mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
      ((cubicThetaAveragedHeat_continuous cubicThetaRadialTestWeight hA).locallyIntegrableOn measurableSet_Ioi)
      (cubicThetaAveragedHeat_top cubicThetaRadialTestWeight hA)
      (cubicThetaAveragedHeat_bottom cubicThetaRadialTestWeight hA 0)
      (s:=(1:ℂ)) (by norm_num)
    simpa only [MellinConvergent,sub_self,Complex.cpow_zero,one_smul] using hm
  have hp : 0<∫ u in Ioi (0:ℝ), (cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re :=
    cubicThetaPositive_setIntegral
      ((Complex.continuous_re.comp_continuousOn
        (cubicThetaAveragedHeat_continuous cubicThetaRadialTestWeight hA))) hi.re
      (fun u hu => (cubicThetaAveragedHeat_test_re_pos hA hu).le) (x:=1) (by norm_num)
      (cubicThetaAveragedHeat_test_re_pos hA (by norm_num))
  have hr := integral_re hi
  change (∫ u in Ioi (0:ℝ), (cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re)=
    (∫ u in Ioi (0:ℝ), cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re at hr
  rw [hr] at hp
  rw [cubicThetaFourierRadialTest_mellin hh,mellin]
  norm_num only [show (2:ℂ)-1-1=0 by norm_num,Complex.cpow_zero,one_smul]
  intro hz
  change 0<(∫ u in Ioi (0:ℝ), cubicThetaAveragedHeat cubicThetaRadialTestWeight A u).re at hp
  rw [hz] at hp
  exact (lt_irrefl 0) hp

end CubicFirstMoment

end

end OAI
