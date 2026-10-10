import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.CoherentPhaseBasis

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

lemma space_ball_real_volume {R : ℝ} (hR : 0 ≤ R) :
    volume.real (ball (0 : Space) R) = (4*Real.pi/3)*R^3 := by
  rw [Measure.real,EuclideanSpace.volume_ball_fin_three,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hR,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

lemma space_ball_second_moment {R : ℝ} (hR : 0 ≤ R) :
    (∫ p : Space in ball 0 R, ‖p‖^2) = (4*Real.pi/5)*R^5 := by
  have he : (∫ p : Space in ball 0 R, ‖p‖^2) =
      ∫ p : Space, (Iio R).indicator (fun t : ℝ => t^2) ‖p‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [Set.indicator,mem_ball,dist_zero_right,mem_Iio]
  rw [he,integral_fun_norm_addHaar volume,space_finrank]
  have hi : (fun t : ℝ => t^(3-1) • (Iio R).indicator (fun t : ℝ => t^2) t) =
      (Iio R).indicator (fun t : ℝ => t^4) := by
    funext t
    by_cases ht : t < R <;> simp only [Set.indicator,mem_Iio,ht,ite_true,ite_false,smul_eq_mul] <;> ring
  rw [hi,setIntegral_indicator measurableSet_Iio]
  have hs : Ioi (0 : ℝ) ∩ Iio R = Ioo 0 R := by ext t; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]
  rw [hs,← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le hR,integral_pow]
  rw [space_ball_real_volume (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [smul_eq_mul]
  ring

def fermiRadius (ρ : Space → ℝ) (z : Space) : ℝ := (3*Real.pi^2*ρ z)^(1/3 : ℝ)

lemma fermiRadius_nonneg {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    0 ≤ fermiRadius ρ z := Real.rpow_nonneg (mul_nonneg (by positivity) (hρ z)) _

lemma fermiRadius_cube {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    (fermiRadius ρ z)^3 = 3*Real.pi^2*ρ z := by
  rw [fermiRadius,← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ z) : 0 ≤ 3*Real.pi^2*ρ z)]
  norm_num

lemma fermiRadius_ball_mass {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    2*coherentFactor*volume.real (ball (0 : Space) (fermiRadius ρ z)) = ρ z := by
  rw [space_ball_real_volume (fermiRadius_nonneg hρ z),fermiRadius_cube hρ z,coherentFactor]
  field_simp [Real.pi_ne_zero]
  ring

lemma fermiRadius_ball_kinetic {ρ : Space → ℝ} (hρ : ∀ z, 0 ≤ ρ z) (z : Space) :
    coherentFactor*(∫ p : Space in ball 0 (fermiRadius ρ z), ‖p‖^2) =
      tfKinetic*(ρ z)^(5/3 : ℝ) := by
  rw [space_ball_second_moment (fermiRadius_nonneg hρ z),fermiRadius,
    ← Real.rpow_mul_natCast (mul_nonneg (by positivity) (hρ z) : 0 ≤ 3*Real.pi^2*ρ z)]
  norm_num only [Nat.cast_ofNat]
  rw [Real.mul_rpow (by positivity : 0 ≤ 3*Real.pi^2) (hρ z)]
  have he : (3*Real.pi^2)^(5/3 : ℝ) = (3*Real.pi^2)*(3*Real.pi^2)^(2/3 : ℝ) := by
    rw [show (5/3 : ℝ)=1+2/3 by ring,Real.rpow_add (by positivity : 0 < 3*Real.pi^2),Real.rpow_one]
  rw [he]
  unfold coherentFactor tfKinetic
  field_simp [Real.pi_ne_zero]
  ring

end CoulombAtom

end

end OAI
