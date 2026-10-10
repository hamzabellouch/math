import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.RadialAxis

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis

lemma integral_norm_rpow_ball {R p : ℝ} (hR : 0 < R) (hp : -3 < p) :
    (∫ x : TFSpace in ball 0 R, ‖x‖^p) =
      (4*Real.pi/(p+3))*R^(p+3) := by
  rw [← integral_indicator measurableSet_ball]
  have he : (ball (0 : TFSpace) R).indicator (fun x => ‖x‖^p) =
      fun x => (Iio R).indicator (fun r : ℝ => r^p) ‖x‖ := by
    funext x
    simp only [indicator,mem_ball_zero_iff,mem_Iio]
  rw [he,tfSpace_radial_integral]
  have hind : (fun r : ℝ => r^2*((Iio R).indicator (fun z : ℝ => z^p) r)) =
      (Iio R).indicator (fun r : ℝ => r^2*r^p) := by
    funext r
    by_cases h : r < R <;> simp [h]
  rw [hind,integral_indicator measurableSet_Iio]
  have hset : Iio R ∩ Ioi (0:ℝ) = Ioo 0 R := by ext r; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]; tauto
  rw [Measure.restrict_restrict measurableSet_Iio,hset]
  have he2 : (∫ r : ℝ in Ioo 0 R, r^2*r^p) = ∫ r : ℝ in Ioo 0 R, r^(p+2) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [← Real.rpow_natCast r 2,← Real.rpow_add hr.1]
    congr 1
    ring
  rw [he2,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR.le]
  rw [integral_rpow (Or.inl (by linarith : -1 < p+2))]
  rw [Real.zero_rpow (by linarith : p+2+1 ≠ 0)]
  have hp3 : p+2+1 = p+3 := by ring
  rw [hp3]
  ring

lemma integral_coulomb_power_ball {R : ℝ} (hR : 0 < R) :
    (∫ x : TFSpace in ball 0 R, ‖x‖^(-5/2:ℝ)) = 8*Real.pi*R^(1/2:ℝ) := by
  have hh := integral_norm_rpow_ball hR (by norm_num : (-3:ℝ) < -5/2)
  norm_num at hh
  norm_num only [neg_div] at ⊢
  rw [hh]
  ring

lemma integral_coulomb_ball {R : ℝ} (hR : 0 < R) :
    (∫ x : TFSpace in ball 0 R, ‖x‖⁻¹) = 2*Real.pi*R^2 := by
  have hh := integral_norm_rpow_ball hR (by norm_num : (-3:ℝ) < -1)
  norm_num [Real.rpow_neg_one] at hh
  rw [hh]
  ring

end CoulombAnalysis

end

end OAI
