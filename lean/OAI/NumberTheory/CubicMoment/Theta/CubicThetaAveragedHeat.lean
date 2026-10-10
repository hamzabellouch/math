import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialTestMass

namespace OAI

/-! Averaging the dilated heat kernel against a fixed radial test preserves
exponential decay at both endpoints of its Mellin variable. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics
open scoped CompactlySupported Topology
namespace CubicFirstMoment

def cubicThetaAveragedHeat (W : C_c(ℝ,ℂ)) (A u : ℝ) : ℂ :=
  ∫ v in Ioi (2:ℝ), star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u

lemma cubicThetaLinearHeat_average_bound (W : C_c(ℝ,ℂ)) {A u v : ℝ}
    (hA : 0<A) (hu : 0<u) (hv : 2<v) :
    ‖star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u‖≤
      (‖W v‖/v^2)*‖cubicThetaDoubleHeat 1 A u‖ := by
  have he : -v*u-A*v/u≤-(1:ℝ)^2*u-A/u := by
    have h₁ := mul_le_mul_of_nonneg_right (show (1:ℝ)≤v by linarith) hu.le
    have h₂ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (show (1:ℝ)≤v by linarith) hA.le) hu.le
    norm_num only [one_pow,neg_one_mul,one_mul,mul_one] at h₁ h₂ ⊢
    linarith
  simp only [norm_mul,norm_div,norm_star,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,sq_abs,cubicThetaLinearHeat,cubicThetaDoubleHeat,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))

lemma cubicThetaDoubleHeat_norm_le_one {A u : ℝ} (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaDoubleHeat 1 A u‖≤1 := by
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  have hp : 0<A/u := div_pos hA hu
  nlinarith

lemma cubicThetaAveragedHeat_integrable (W : C_c(ℝ,ℂ)) {A u : ℝ}
    (hA : 0<A) (hu : 0<u) :
    IntegrableOn (fun v : ℝ => star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u)
      (Ioi (2:ℝ)) := by
  apply (cubicThetaRadialWeight_integrable W).mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (cubicThetaLinearHeat_average_bound W hA hu hv).trans
    ((mul_le_mul_of_nonneg_left (cubicThetaDoubleHeat_norm_le_one hA hu)
      (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))

lemma cubicThetaAveragedHeat_bound (W : C_c(ℝ,ℂ)) {A u : ℝ}
    (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaAveragedHeat W A u‖≤
      cubicThetaRadialWeightMass W*‖cubicThetaDoubleHeat 1 A u‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [cubicThetaRadialWeightMass,← integral_mul_const]
  apply integral_mono_ae (cubicThetaAveragedHeat_integrable W hA hu).norm
    ((cubicThetaRadialWeight_integrable W).mul_const _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cubicThetaLinearHeat_average_bound W hA hu hv

lemma cubicThetaAveragedHeat_continuous (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) :
    ContinuousOn (cubicThetaAveragedHeat W A) (Ioi (0:ℝ)) := by
  apply continuousOn_of_dominated
    (bound:=fun v : ℝ => ‖W v‖/v^2)
  · intro u hu
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop
  · intro u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (cubicThetaLinearHeat_average_bound W hA hu hv).trans
      ((mul_le_mul_of_nonneg_left (cubicThetaDoubleHeat_norm_le_one hA hu)
        (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))
  · exact cubicThetaRadialWeight_integrable W
  · filter_upwards with v
    have hc : ContinuousOn (fun u : ℝ => -v*u-A*v/u) (Ioi 0) :=
      (continuousOn_const.mul continuousOn_id).sub
        (continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt hu))
    exact continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hc))

lemma cubicThetaAveragedHeat_top (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) :
    cubicThetaAveragedHeat W A =O[atTop] (fun u : ℝ => Real.exp (-(1:ℝ)*u)) := by
  have ht : cubicThetaDoubleHeat 1 A =O[atTop] (fun u : ℝ => Real.exp (-(1:ℝ)*u)) := by
    simpa only [one_pow] using cubicThetaDoubleHeat_top 1 hA
  apply IsBigO.trans ?_ ht
  apply IsBigO.of_bound (cubicThetaRadialWeightMass W)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  exact cubicThetaAveragedHeat_bound W hA hu

lemma cubicThetaAveragedHeat_bottom (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) (b : ℝ) :
    cubicThetaAveragedHeat W A =O[𝓝[>] 0] (fun u : ℝ => u^(-b)) := by
  apply IsBigO.trans ?_ (cubicThetaDoubleHeat_bottom 1 hA b)
  apply IsBigO.of_bound (cubicThetaRadialWeightMass W)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact cubicThetaAveragedHeat_bound W hA hu

lemma cubicThetaAveragedHeat_mellinConvergent (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A)
    (s : ℂ) : MellinConvergent (cubicThetaAveragedHeat W A) s := by
  exact mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
    ((cubicThetaAveragedHeat_continuous W hA).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaAveragedHeat_top W hA) (cubicThetaAveragedHeat_bottom W hA (s.re-1))
    (by linarith)

theorem cubicThetaAveragedHeat_mellin_entire (W : C_c(ℝ,ℂ)) {A : ℝ} (hA : 0<A) :
    Differentiable ℂ (mellin (cubicThetaAveragedHeat W A)) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
    ((cubicThetaAveragedHeat_continuous W hA).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaAveragedHeat_top W hA) (cubicThetaAveragedHeat_bottom W hA (s.re-1))
    (by linarith)

end CubicFirstMoment

end

end OAI
