import Mathlib
import OAI.Analysis.CoulombRadii.Localization.TruncatedCoulomb

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

lemma coulombKernel_fiveHalves_integrableOn_ball (R : ℝ) :
    IntegrableOn (fun x : Space => coulombKernel x^(5/2:ℝ)) (Metric.ball 0 R) := by
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 5/2) (by simp) (by norm_num)
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (coulombKernel_nonneg _) _)]
    simp only [coulombKernel,Real.inv_rpow (norm_nonneg _),one_mul]
    rw [Real.rpow_neg (norm_nonneg _)]
  · exact (coulombKernel_measurable.pow_const _).aestronglyMeasurable

lemma coulombKernel_fiveHalves_ball_integral {R : ℝ} (hR : 0≤R) :
    (∫ x : Space in Metric.ball 0 R, coulombKernel x^(5/2:ℝ)) =
      8*Real.pi*R^(1/2:ℝ) := by
  have H := integral_fun_norm_addHaar (volume : Measure Space)
    (fun t : ℝ => if t<R then t^(-5/2:ℝ) else 0)
  have hleft : (∫ x : Space in Metric.ball 0 R, coulombKernel x^(5/2:ℝ)) =
      ∫ x : Space, if ‖x‖<R then ‖x‖^(-5/2:ℝ) else 0 := by
    rw [←integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : ‖x‖<R
    · simp [Set.indicator,Metric.mem_ball,dist_zero_right,hx,coulombKernel,
        Real.inv_rpow (norm_nonneg _),Real.rpow_neg (norm_nonneg _),neg_div]
    · simp [Set.indicator,Metric.mem_ball,dist_zero_right,hx]
  rw [hleft,H]
  have hball : volume.real (Metric.ball (0:Space) 1)=4*Real.pi/3 := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hdim : Module.finrank ℝ Space=3 := by simp [Space]
  simp only [hdim,hball,nsmul_eq_mul,smul_eq_mul]
  have hint : (∫ t in Ioi (0:ℝ),t^(3-1)*(if t<R then t^(-5/2:ℝ) else 0))=
      ∫ t in Ioo 0 R, t^(-1/2:ℝ) := by
    calc
      _=∫ t in Ioi (0:ℝ), (Iio R).indicator (fun t : ℝ => t^(-1/2:ℝ)) t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        by_cases h : t<R
        · simp only [h,ite_true,Set.indicator,mem_Iio]
          have ht' : 0<t := ht
          norm_num only
          rw [←Real.rpow_natCast t 2,←Real.rpow_add ht']
          norm_num
        · simp [Set.indicator,h]
      _=_ := by rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
        inter_comm,Ioi_inter_Iio]
  rw [hint,setIntegral_congr_set Ioo_ae_eq_Ioc,←intervalIntegral.integral_of_le hR,
    integral_rpow (Or.inl (by norm_num : (-1:ℝ)< -1/2))]
  norm_num
  ring

lemma translated_coulomb_power_ball_integral (y : Space) {R : ℝ} (hR : 0≤R) :
    (∫ x in Metric.ball y R, coulombKernel (y-x)^(5/2:ℝ))=8*Real.pi*R^(1/2:ℝ) := by
  have he : (Metric.ball y R).indicator (fun x => coulombKernel (y-x)^(5/2:ℝ))=
      fun x => (Metric.ball (0:Space) R).indicator (fun z => coulombKernel z^(5/2:ℝ)) (y-x) := by
    funext x
    have hh : y-x∈Metric.ball (0:Space) R ↔ x∈Metric.ball y R := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hx : x∈Metric.ball y R <;> simp [hh,hx]
  rw [←integral_indicator measurableSet_ball,he,integral_sub_left_eq_self,
    integral_indicator measurableSet_ball,coulombKernel_fiveHalves_ball_integral hR]

lemma translated_coulomb_memLp_fiveHalves (y : Space) (R : ℝ) :
    MemLp (fun x => coulombKernel (y-x)) (ENNReal.ofReal (5/2:ℝ))
      (volume.restrict (Metric.ball y R)) := by
  apply (integrable_norm_rpow_iff
    ((coulombKernel_measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (by norm_num : ENNReal.ofReal (5/2:ℝ)≠0) (by simp)).mp
  norm_num only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/2)]
  change IntegrableOn (fun x => ‖coulombKernel (y-x)‖^(5/2:ℝ)) (Metric.ball y R)
  simp only [Real.norm_of_nonneg (coulombKernel_nonneg _)]
  rw [←integrable_indicator_iff measurableSet_ball]
  have he : (Metric.ball y R).indicator (fun x => coulombKernel (y-x)^(5/2:ℝ))=
      fun x => (Metric.ball (0:Space) R).indicator (fun z => coulombKernel z^(5/2:ℝ)) (y-x) := by
    funext x
    have hh : y-x∈Metric.ball (0:Space) R ↔ x∈Metric.ball y R := by
      simp only [Metric.mem_ball,dist_eq_norm,sub_zero,norm_sub_rev]
    by_cases hx : x∈Metric.ball y R <;> simp [hh,hx]
  rw [he]
  exact (integrable_comp_sub_left _ y).mpr
    ((coulombKernel_fiveHalves_integrableOn_ball R).integrable_indicator measurableSet_ball)

theorem near_coulomb_holder {ρ : Space → ℝ} (y : Space) {R : ℝ} (hR : 0≤R)
    (hρ : MemLp ρ (ENNReal.ofReal (5/3:ℝ)) (volume.restrict (Metric.ball y R)))
    (hp : 0≤ᵐ[volume.restrict (Metric.ball y R)] ρ) :
    (∫ x in Metric.ball y R, ρ x*coulombKernel (y-x))≤
      (∫ x in Metric.ball y R, ρ x^(5/3:ℝ))^(3/5:ℝ)*
        ((8*Real.pi)^(2/5:ℝ)*R^(1/5:ℝ)) := by
  have hc : (5/3:ℝ).HolderConjugate (5/2:ℝ) := by
    rw [Real.holderConjugate_iff]; norm_num
  have H := integral_mul_le_Lp_mul_Lq_of_nonneg hc hp
    (Eventually.of_forall (fun x => coulombKernel_nonneg (y-x))) hρ
    (translated_coulomb_memLp_fiveHalves y R)
  rw [translated_coulomb_power_ball_integral y hR] at H
  norm_num only at H
  convert H using 1
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤8*Real.pi) (Real.rpow_nonneg hR _),
    ←Real.rpow_mul hR]
  norm_num

end Coulomb
end

end
end

end OAI
