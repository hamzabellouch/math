import OAI.MeasureTheory.Falconer.Radial.PlateScales
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! # Summable tails of the actual dyadic plate loss bounds -/

namespace Falconer
open Filter
open scoped ENNReal Topology

theorem plateScale_add_power (J n : ℕ) (t : ℝ) :
    (plateScale (J+n))^t = (plateScale J)^t*((2:ℝ)^(-t))^n := by
  simp only [plateScale_rpow,pow_add]

theorem summable_plate_loss (J : ℕ) (B : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (fun n => B*(plateScale (J+n))^t) := by
  have hs := (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-t))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht))).mul_left
      (B*(plateScale J)^t)
  simpa only [plateScale_add_power,mul_assoc] using hs

theorem plate_loss_tsum (J : ℕ) {B t : ℝ} (hB : 0 ≤ B) (ht : 0 < t) :
    (∑' n : ℕ, ENNReal.ofReal (B*(plateScale (J+n))^t)) =
      ENNReal.ofReal (B*(plateScale J)^t/(1-(2:ℝ)^(-t))) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n =>
    mul_nonneg hB (Real.rpow_nonneg (plateScale_pos _).le _)) (summable_plate_loss J B ht)]
  congr 1
  simp_rw [plateScale_add_power,← mul_assoc]
  rw [tsum_mul_left,tsum_geometric_of_lt_one
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-t))
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos ht)),div_eq_mul_inv]

theorem plate_loss_real_tail_tendsto (B : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun J => B*(plateScale J)^t/(1-(2:ℝ)^(-t))) atTop (𝓝 (0:ℝ)) := by
  simpa only [mul_zero,zero_div] using
    ((plateScale_power_tendsto ht).const_mul B).div_const (1-(2:ℝ)^(-t))

theorem eventually_plate_loss_tail {B t η : ℝ} (hB : 0 ≤ B) (ht : 0 < t) (hη : 0 < η) :
    ∀ᶠ J : ℕ in atTop,
      (∑' n : ℕ, ENNReal.ofReal (B*(plateScale (J+n))^t)) < ENNReal.ofReal η := by
  have he := (plate_loss_real_tail_tendsto B ht).eventually (eventually_lt_nhds hη)
  filter_upwards [he] with J hJ
  rw [plate_loss_tsum J hB ht]
  exact ENNReal.ofReal_lt_ofReal_iff hη |>.mpr hJ

end Falconer

end OAI
