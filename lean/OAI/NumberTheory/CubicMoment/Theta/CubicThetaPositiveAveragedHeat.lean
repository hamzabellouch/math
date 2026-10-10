import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAveragedHeat
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveRadialNormalization

namespace OAI

/-! The radial Mellin kernel at an arbitrary positive cutoff. Its
endpoint decay follows from the same double heat kernel, with rescaled parameters. -/
noncomputable section
open Set MeasureTheory Filter Asymptotics Topology
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaPositiveAveragedHeat (W : C_c(ℝ,ℂ)) (ε A u : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u

def cubicThetaPositiveRadialWeightMass (W : C_c(ℝ,ℂ)) (ε : ℝ) : ℝ :=
  ∫ v in Ioi ε,‖W v‖/v^2

lemma cubicThetaPositiveRadialWeight_integrable (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε) :
    IntegrableOn (fun v : ℝ => ‖W v‖/v^2) (Ioi ε) := by
  have hi : Integrable (fun v : ℝ => ‖W v‖) :=
    (W.continuous.integrable_of_hasCompactSupport W.hasCompactSupport).norm
  apply (hi.div_const (ε^2)).integrableOn.mono' (by
    apply Measurable.aestronglyMeasurable
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv' : ε<v := hv
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))]
  apply div_le_div_of_nonneg_left (_root_.norm_nonneg _) (sq_pos_of_pos hε)
  nlinarith

lemma cubicThetaPositiveLinearHeat_bound (W : C_c(ℝ,ℂ)) {ε A u v : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) (hv : ε<v) :
    ‖star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u‖≤
      (‖W v‖/v^2)*‖cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖ := by
  have he : -v*u-A*v/u≤-(Real.sqrt ε)^2*u-(A*ε)/u := by
    rw [Real.sq_sqrt hε.le]
    have h₁ := mul_le_mul_of_nonneg_right hv.le hu.le
    have h₂ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv.le hA.le) hu.le
    linarith
  simp only [norm_mul,norm_div,norm_star,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    cubicThetaLinearHeat,cubicThetaDoubleHeat,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))

lemma cubicThetaPositiveDoubleHeat_norm_le_one {ε A u : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖≤1 := by
  rw [cubicThetaDoubleHeat,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  have h₁ := mul_pos hε hu
  have h₂ := div_pos (mul_pos hA hε) hu
  rw [Real.sq_sqrt hε.le]
  linarith

lemma cubicThetaPositiveAveragedHeat_integrable (W : C_c(ℝ,ℂ)) {ε A u : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) :
    IntegrableOn (fun v : ℝ => star (W v)/(v:ℂ)^2*cubicThetaLinearHeat v A u)
      (Ioi ε) := by
  apply (cubicThetaPositiveRadialWeight_integrable W hε).mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact (cubicThetaPositiveLinearHeat_bound W hε hA hu hv).trans
    ((mul_le_mul_of_nonneg_left (cubicThetaPositiveDoubleHeat_norm_le_one hε hA hu)
      (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))

lemma cubicThetaPositiveAveragedHeat_bound (W : C_c(ℝ,ℂ)) {ε A u : ℝ}
    (hε : 0<ε) (hA : 0<A) (hu : 0<u) :
    ‖cubicThetaPositiveAveragedHeat W ε A u‖≤
      cubicThetaPositiveRadialWeightMass W ε*‖cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) u‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [cubicThetaPositiveRadialWeightMass,←integral_mul_const]
  apply integral_mono_ae (cubicThetaPositiveAveragedHeat_integrable W hε hA hu).norm
    ((cubicThetaPositiveRadialWeight_integrable W hε).mul_const _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact cubicThetaPositiveLinearHeat_bound W hε hA hu hv

lemma cubicThetaPositiveAveragedHeat_continuous (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) :
    ContinuousOn (cubicThetaPositiveAveragedHeat W ε A) (Ioi (0:ℝ)) := by
  apply continuousOn_of_dominated (bound:=fun v : ℝ => ‖W v‖/v^2)
  · intro u hu
    apply Measurable.aestronglyMeasurable
    unfold cubicThetaLinearHeat
    fun_prop
  · intro u hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact (cubicThetaPositiveLinearHeat_bound W hε hA hu hv).trans
      ((mul_le_mul_of_nonneg_left (cubicThetaPositiveDoubleHeat_norm_le_one hε hA hu)
        (div_nonneg (_root_.norm_nonneg _) (sq_nonneg _))).trans_eq (mul_one _))
  · exact cubicThetaPositiveRadialWeight_integrable W hε
  · filter_upwards with v
    have hc : ContinuousOn (fun u : ℝ => -v*u-A*v/u) (Ioi 0) :=
      (continuousOn_const.mul continuousOn_id).sub
        (continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt hu))
    exact continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hc))

lemma cubicThetaPositiveAveragedHeat_top (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) :
    cubicThetaPositiveAveragedHeat W ε A =O[atTop] (fun u : ℝ => Real.exp (-ε*u)) := by
  have ht : cubicThetaDoubleHeat (Real.sqrt ε) (A*ε) =O[atTop]
      (fun u : ℝ => Real.exp (-ε*u)) := by
    simpa only [Real.sq_sqrt hε.le] using cubicThetaDoubleHeat_top (Real.sqrt ε) (mul_pos hA hε)
  apply IsBigO.trans ?_ ht
  apply IsBigO.of_bound (cubicThetaPositiveRadialWeightMass W ε)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
  exact cubicThetaPositiveAveragedHeat_bound W hε hA hu

lemma cubicThetaPositiveAveragedHeat_bottom (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) (b : ℝ) :
    cubicThetaPositiveAveragedHeat W ε A =O[𝓝[>] 0] (fun u : ℝ => u^(-b)) := by
  apply IsBigO.trans ?_ (cubicThetaDoubleHeat_bottom (Real.sqrt ε) (mul_pos hA hε) b)
  apply IsBigO.of_bound (cubicThetaPositiveRadialWeightMass W ε)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact cubicThetaPositiveAveragedHeat_bound W hε hA hu

theorem cubicThetaPositiveAveragedHeat_mellin_entire (W : C_c(ℝ,ℂ)) {ε A : ℝ}
    (hε : 0<ε) (hA : 0<A) :
    Differentiable ℂ (mellin (cubicThetaPositiveAveragedHeat W ε A)) := by
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp hε
    ((cubicThetaPositiveAveragedHeat_continuous W hε hA).locallyIntegrableOn measurableSet_Ioi)
    (cubicThetaPositiveAveragedHeat_top W hε hA)
    (cubicThetaPositiveAveragedHeat_bottom W hε hA (s.re-1)) (by linarith)

end CubicFirstMoment

end

end OAI
