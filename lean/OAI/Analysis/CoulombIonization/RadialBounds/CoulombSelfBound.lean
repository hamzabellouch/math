import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombNear
import OAI.Analysis.CoulombIonization.RadialBounds.MomentumBall

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

lemma inv_norm_integrable_ball (r : ℝ) :
    IntegrableOn (fun x : Space => ‖x‖⁻¹) (ball 0 r) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp [Space])
    (show (1:ℝ) < Module.finrank ℝ Space by rw [space_finrank]; norm_num) (C := 1)
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),Real.rpow_neg_one,one_mul,le_refl]
  · exact measurable_norm.inv.aestronglyMeasurable

lemma space_ball_coulomb_integral {r : ℝ} (hr : 0 ≤ r) :
    (∫ x : Space in ball 0 r, ‖x‖⁻¹) = 2*Real.pi*r^2 := by
  have he : (∫ x : Space in ball 0 r, ‖x‖⁻¹) =
      ∫ x : Space, (Iio r).indicator (fun t : ℝ => t⁻¹) ‖x‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [Set.indicator,mem_ball,dist_zero_right,mem_Iio]
  rw [he,integral_fun_norm_addHaar volume,space_finrank]
  have hi : (fun t : ℝ => t^(3-1) • (Iio r).indicator (fun t : ℝ => t⁻¹) t) =
      (Iio r).indicator (fun t : ℝ => t) := by
    funext t
    by_cases ht : t < r
    · simp only [Set.indicator,mem_Iio,ht,ite_true,smul_eq_mul]
      by_cases hz : t=0
      · simp [hz]
      · norm_num
        field_simp
    · simp only [Set.indicator,mem_Iio,ht,ite_false,smul_eq_mul,mul_zero]
  rw [hi,setIntegral_indicator measurableSet_Iio]
  have hs : Ioi (0 : ℝ) ∩ Iio r = Ioo 0 r := by ext t; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]
  rw [hs,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hr,integral_id]
  rw [space_ball_real_volume (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [smul_eq_mul]
  ring

lemma shifted_truncated_coulomb_integrable (a : Space) (r : ℝ) :
    Integrable ((ball a r).indicator (fun y : Space => ‖a-y‖⁻¹)) := by
  have hi := ((inv_norm_integrable_ball r).integrable_indicator measurableSet_ball).comp_sub_right a
  apply hi.congr
  filter_upwards [] with x
  simp only [Set.indicator,mem_ball,dist_eq_norm,sub_zero,norm_sub_rev a x]

lemma shifted_truncated_coulomb_integral (a : Space) {r : ℝ} (hr : 0 ≤ r) :
    (∫ y : Space, (ball a r).indicator (fun y : Space => ‖a-y‖⁻¹) y) = 2*Real.pi*r^2 := by
  calc
    _ = ∫ y : Space, (ball 0 r).indicator (fun y : Space => ‖y‖⁻¹) (y-a) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Set.indicator,mem_ball,dist_eq_norm,sub_zero,norm_sub_rev a x]
    _ = ∫ y : Space in ball 0 r, ‖y‖⁻¹ := by rw [integral_sub_right_eq_self,integral_indicator measurableSet_ball]
    _ = _ := space_ball_coulomb_integral hr

lemma bounded_density_potential_bound {η : Space → ℝ} (hη : Integrable η)
    (hp : MemLp η (5/3 : ENNReal)) (hn : ∀ x, 0 ≤ η x) {B : ℝ} (hb : ∀ x, η x ≤ B)
    {r : ℝ} (hr : 0 < r) (a : Space) :
    CoulombAnalysis.tfPotential η a ≤ B*(2*Real.pi*r^2)+(∫ y : Space, η y)/r := by
  have hi : Integrable (fun x : Space => B*(ball a r).indicator (fun y : Space => ‖a-y‖⁻¹) x + η x/r) :=
    ((shifted_truncated_coulomb_integrable a r).const_mul B).add (hη.div_const r)
  have he := integral_mono (CoulombAnalysis.tfPotential_integrable hη hp a) hi (fun y => ?_)
  · simpa only [CoulombAnalysis.tfPotential,integral_add ((shifted_truncated_coulomb_integrable a r).const_mul B)
      (hη.div_const r),integral_const_mul,shifted_truncated_coulomb_integral a hr.le,integral_div] using he
  · by_cases hy : y ∈ ball a r
    · rw [Set.indicator_of_mem hy]
      calc
        η y/‖a-y‖ ≤ B*‖a-y‖⁻¹ := by simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hb y) (inv_nonneg.mpr (norm_nonneg _))
        _ ≤ _ := le_add_of_nonneg_right (div_nonneg (hn y) hr.le)
    · rw [Set.indicator_of_notMem hy,mul_zero,zero_add]
      have hy' : r ≤ ‖a-y‖ := by simpa only [mem_ball,dist_eq_norm,not_lt,norm_sub_rev y a] using hy
      exact div_le_div_of_nonneg_left (hn y) hr hy'

end CoulombAtom

end

end OAI
