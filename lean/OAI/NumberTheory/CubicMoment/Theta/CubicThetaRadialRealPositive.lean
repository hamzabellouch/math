import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialNonzero

namespace OAI

/-! The chosen test has no real zeros, throughout the spectral line. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaRadialMellin_real_part (σ : ℝ) {u : ℝ} (hu : 0<u) (z : ℂ) :
    ((u:ℂ)^((σ:ℂ)-2)*z).re=u^(σ-2)*z.re := by
  rw [show (σ:ℂ)-2=((σ-2:ℝ):ℂ) by push_cast; rfl,
    ← Complex.ofReal_cpow hu.le,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

theorem cubicThetaFourierRadialTest_real_pos {h : Eisenstein} (hh : h≠0) (σ : ℝ) :
    0<(cubicThetaFourierRadialTest h cubicThetaRadialTestWeight σ).re := by
  let A := cubicThetaRowHeatScale h
  have hA : 0<A := cubicThetaRowHeatScale_pos hh
  let F := fun u : ℝ => (u:ℂ)^((σ:ℂ)-2)*cubicThetaAveragedHeat cubicThetaRadialTestWeight A u
  have hi : IntegrableOn F (Ioi (0:ℝ)) := by
    have hm := cubicThetaAveragedHeat_mellinConvergent cubicThetaRadialTestWeight hA ((σ:ℂ)-1)
    simpa only [MellinConvergent,smul_eq_mul,show (σ:ℂ)-1-1=(σ:ℂ)-2 by ring] using hm
  have hc : ContinuousOn (fun u => (F u).re) (Ioi (0:ℝ)) := by
    intro u hu
    have hp := Complex.continuousAt_ofReal_cpow_const u ((σ:ℂ)-2) (Or.inr (ne_of_gt hu))
    have ha := (cubicThetaAveragedHeat_continuous cubicThetaRadialTestWeight hA).continuousAt
      (isOpen_Ioi.mem_nhds hu)
    exact (Complex.continuous_re.continuousAt.comp (hp.mul ha)).continuousWithinAt
  have hp : ∀ u∈Ioi (0:ℝ), 0<(F u).re := by
    intro u hu
    dsimp only [F]
    rw [cubicThetaRadialMellin_real_part σ hu]
    exact mul_pos (Real.rpow_pos_of_pos hu _) (cubicThetaAveragedHeat_test_re_pos hA hu)
  have hpos := cubicThetaPositive_setIntegral hc hi.re (fun u hu => (hp u hu).le)
    (x:=1) (by norm_num) (hp 1 (by norm_num))
  have hr := integral_re hi
  change (∫ u in Ioi (0:ℝ), (F u).re)=(∫ u in Ioi (0:ℝ), F u).re at hr
  rw [hr] at hpos
  rw [cubicThetaFourierRadialTest_mellin hh,mellin]
  simpa only [show (σ:ℂ)-1-1=(σ:ℂ)-2 by ring,smul_eq_mul] using hpos

end CubicFirstMoment

end

end OAI
