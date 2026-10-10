import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogSavingPowers
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! Conductor powers measured at the full convolution length transfer
to each rough coordinate, with one additional logarithmic power. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma rough_coordinate_conductor_scale {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ, L^c ≤ Y →
      (Real.log L)^A ≤ (Real.log Y)^(A+1) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop ((c⁻¹)^A/c)] with L hL hlog
  intro Y hY
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hYp : 0 < Y := (Real.rpow_pos_of_pos hLp c).trans_le hY
  have hlogs : c*Real.log L ≤ Real.log Y := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hLp c) hY
    rwa [Real.log_rpow hLp] at h
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  have hmul : (c⁻¹)^A ≤ c*Real.log L := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hlog
  have hlogY : 0 < Real.log Y := by
    have hpos : 0 < (c⁻¹)^A := Real.rpow_pos_of_pos (inv_pos.mpr hc) _
    exact hpos.trans_le (hmul.trans hlogs)
  have hcomp : Real.log L ≤ c⁻¹*Real.log Y := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).mpr (by nlinarith)
  calc
    _ ≤ (c⁻¹*Real.log Y)^A := Real.rpow_le_rpow hlogL hcomp hA
    _ = (c⁻¹)^A*(Real.log Y)^A := Real.mul_rpow (inv_nonneg.mpr hc.le) hlogY.le
    _ ≤ Real.log Y*(Real.log Y)^A := mul_le_mul_of_nonneg_right
      (hmul.trans hlogs) (Real.rpow_nonneg hlogY.le _)
    _ = _ := by rw [Real.rpow_add hlogY,Real.rpow_one]; ring

end CubicFirstMoment

end

end OAI
