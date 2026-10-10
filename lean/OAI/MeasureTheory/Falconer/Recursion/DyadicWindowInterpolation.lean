import OAI.MeasureTheory.Falconer.Radial.RadialScaleWindow
import OAI.MeasureTheory.Falconer.Recursion.RelativeScaleBudget
import OAI.MeasureTheory.Falconer.Radial.RadialDyadicBracket

namespace OAI

/-! # From a window of improved dyadic caps to every radius -/

namespace Falconer
open scoped ENNReal

theorem dyadic_window_interpolation (f : ℝ → ℝ≥0∞) (hf : Monotone f)
    (hmass : ∀ r : ℝ, f r ≤ 1) {N m : ℕ} (_hmN : m ≤ N)
    {e q v : ℝ} (hq : 0 ≤ q) (hqv : q ≤ v)
    (hcoarse : (m:ℝ)*q ≤ (N:ℝ)*e)
    (hconstant : (2:ℝ)^v ≤ ((2:ℝ)^N)^e)
    (hdyadic : ∀ j : ℕ, m ≤ j → j ≤ N → f (1/(2:ℝ)^j) ≤
      ENNReal.ofReal ((1/(2:ℝ)^j)^v))
    {r : ℝ} (hr : 1/(2:ℝ)^N ≤ r) (hr1 : r ≤ 1) :
    f r ≤ ENNReal.ofReal (((2:ℝ)^N)^e*r^q) := by
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hc : 1/(2:ℝ)^m ≤ r
  · apply (hmass r).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hp := dyadic_relative_scale_bound m N hcoarse
    have hi : ((2:ℝ)^m)^q*(1/(2:ℝ)^m)^q = 1 := by
      rw [one_div,Real.inv_rpow (by positivity)]
      exact mul_inv_cancel₀ (by positivity)
    calc
      1 = ((2:ℝ)^m)^q*(1/(2:ℝ)^m)^q := hi.symm
      _ ≤ ((2:ℝ)^N)^e*r^q := mul_le_mul hp
        (Real.rpow_le_rpow (by positivity) hc hq) (by positivity) (by positivity)
  · obtain ⟨j,hj,hrj,hjr⟩ := Regularization.dyadic_radius_bracket hr hr1
    have hmj : m ≤ j := by
      by_contra hn
      have hjm : j+1 ≤ m := by omega
      have hd : 1/(2:ℝ)^m ≤ 1/(2:ℝ)^(j+1) :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hjm)
      have he : 1/(2:ℝ)^j = 2*(1/(2:ℝ)^(j+1)) := by rw [pow_succ]; field_simp
      have hh : 1/(2:ℝ)^(j+1) ≤ r := by rw [he] at hjr; linarith only [hjr]
      exact hc (hd.trans hh)
    apply ((hf hrj).trans (hdyadic j hmj hj)).trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      _ ≤ (2*r)^v := Real.rpow_le_rpow (by positivity) hjr (hq.trans hqv)
      _ = (2:ℝ)^v*r^v := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ ((2:ℝ)^N)^e*r^q := mul_le_mul hconstant
        (Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hqv) (by positivity) (by positivity)

end Falconer

end OAI
