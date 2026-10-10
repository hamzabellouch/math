import OAI.MeasureTheory.Falconer.Angular.GnomonicInverse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! # The one-dimensional radial integral in the gnomonic cone formula -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem lintegral_nonnegative_power_Ioo (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ r : ℝ in Ioo 0 t, ENNReal.ofReal (r^n)) = ENNReal.ofReal (t^(n+1)/(n+1)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_pow n).1,
    ← intervalIntegral.integral_of_le ht]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg hr.1.le _

theorem gnomonic_radial_height_power {n : ℕ} (x : Space n) :
    (‖northLift x‖⁻¹)^(n+1) = gnomonicDensity x := by
  have hn : 0 < ‖northLift x‖ := norm_pos_iff.mpr (northLift_ne_zero x)
  rw [gnomonicDensity,← northLift_norm_sq]
  rw [← Real.rpow_natCast (‖northLift x‖⁻¹),Real.inv_rpow hn.le]
  rw [← Real.rpow_neg hn.le]
  rw [← Real.rpow_natCast ‖northLift x‖ 2,← Real.rpow_mul hn.le]
  congr 1
  push_cast
  ring

theorem gnomonic_radial_integral {n : ℕ} (x : Space n) :
    (∫⁻ r : ℝ in Ioo 0 ‖northLift x‖⁻¹, ENNReal.ofReal (r^n)) =
      ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ)) := by
  rw [lintegral_nonnegative_power_Ioo _ _ (inv_nonneg.mpr (norm_nonneg _)),gnomonic_radial_height_power]
  norm_cast

end Falconer

end OAI
