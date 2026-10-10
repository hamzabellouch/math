import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroRadialMellin

namespace OAI

/-! Positivity of the fixed compact test's real Mellin transforms. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaRadialTestWeight_mellin_pos (r : ℝ) :
    0<(mellin cubicThetaRadialTestWeight (r:ℂ)).re := by
  let F := fun u : ℝ => (u:ℂ)^((r:ℂ)-1)*cubicThetaRadialTestWeight u
  have hsupport : tsupport cubicThetaRadialTestWeight⊆Ioi (0:ℝ) := by
    intro v hv
    exact lt_of_lt_of_le (by norm_num) (cubicThetaRadialTestWeight_tsupport hv).1
  have hi : IntegrableOn F (Ioi (0:ℝ)) := by
    have hm := smooth_mellin_convergent cubicThetaRadialTestWeight
      cubicThetaRadialTestWeight.hasCompactSupport hsupport cubicThetaRadialTestWeight.continuous (r:ℂ)
    exact hm
  have hc : ContinuousOn (fun u => (F u).re) (Ioi (0:ℝ)) := by
    intro u hu
    have hp := Complex.continuousAt_ofReal_cpow_const u ((r:ℂ)-1) (Or.inr (ne_of_gt hu))
    exact (Complex.continuous_re.continuousAt.comp
      (hp.mul cubicThetaRadialTestWeight.continuous.continuousAt)).continuousWithinAt
  have hpart (u : ℝ) (hu : 0<u) : (F u).re=u^(r-1)*cubicThetaRadialTent u := by
    dsimp only [F]
    rw [show (r:ℂ)-1=((r-1:ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hu.le,cubicThetaRadialTestWeight_apply,
      ← Complex.ofReal_mul,Complex.ofReal_re]
  have hp : 0<∫ u in Ioi (0:ℝ), (F u).re := by
    apply cubicThetaPositive_setIntegral hc hi.re
      (fun u hu => (hpart u hu) ▸ mul_nonneg (Real.rpow_nonneg hu.le _) (cubicThetaRadialTent_nonneg u))
      (x:=3) (by norm_num)
    rw [hpart 3 (by norm_num)]
    norm_num only [cubicThetaRadialTent,sub_self,abs_zero,sub_zero,max_eq_right zero_le_one,mul_one]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hr := integral_re hi
  change (∫ u in Ioi (0:ℝ), (F u).re)=(mellin cubicThetaRadialTestWeight (r:ℂ)).re at hr
  rwa [hr] at hp

theorem cubicThetaZeroRadialTest_real_pos (σ : ℝ) :
    0<(cubicThetaZeroRadialTest cubicThetaRadialTestWeight σ).re := by
  rw [cubicThetaZeroRadialTest_mellin]
  simpa only [Complex.ofReal_neg] using cubicThetaRadialTestWeight_mellin_pos (-σ)

end CubicFirstMoment

end

end OAI
