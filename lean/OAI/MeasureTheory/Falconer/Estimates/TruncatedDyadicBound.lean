import OAI.MeasureTheory.Falconer.Radial.PlateScales
import OAI.MeasureTheory.Falconer.Radial.RadialDyadicBracket

namespace OAI

/-! # Uniform interpolation above and below a finite dyadic scale window -/

namespace Falconer
open scoped ENNReal

theorem truncated_dyadic_bound (j₀ J : ℕ) (f : ℝ → ℝ≥0∞) (hf : Monotone f)
    (hmass : ∀ r, f r ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hdyadic : ∀ j, j₀ ≤ j → j ≤ J → f (plateScale j) ≤ ENNReal.ofReal (2*(plateScale j)^b))
    (r : ℝ) :
    f r ≤ ENNReal.ofReal ((max ((plateScale j₀)^(-b)) (2*(2:ℝ)^b))*
      (max r (plateScale J))^b) := by
  let C := max ((plateScale j₀)^(-b)) (2*(2:ℝ)^b)
  let t := max r (plateScale J)
  have hδJ : plateScale J ≤ t := le_max_right _ _
  have ht : 0 < t := (plateScale_pos J).trans_le (le_max_right _ _)
  by_cases hc : plateScale j₀ ≤ t
  · apply (hmass r).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    change 1 ≤ C*t^b
    have he : (plateScale j₀)^(-b)*(plateScale j₀)^b = 1 := by
      rw [← Real.rpow_add (plateScale_pos _),neg_add_cancel,Real.rpow_zero]
    calc
      1 = (plateScale j₀)^(-b)*(plateScale j₀)^b := he.symm
      _ ≤ C*t^b := mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow (plateScale_pos _).le hc hb)
        (Real.rpow_nonneg (plateScale_pos _).le _)
        (by dsimp [C]; exact (Real.rpow_nonneg (plateScale_pos _).le _).trans (le_max_left _ _))
  · have ht0 : t ≤ plateScale j₀ := (not_le.mp hc).le
    obtain ⟨j,hj₀,hjJ,htj,hjt⟩ := radial_dyadic_bracket_above J j₀
      (show ((2:ℝ)^J)⁻¹ ≤ t by simpa only [plateScale_eq,one_div] using hδJ)
      (show t ≤ ((2:ℝ)^j₀)⁻¹ by simpa only [plateScale_eq,one_div] using ht0)
    have htj' : t ≤ plateScale j := by simpa only [plateScale_eq,one_div] using htj
    have hjt' : plateScale j ≤ 2*t := by simpa only [plateScale_eq,one_div] using hjt.le
    apply ((hf ((le_max_left _ _).trans htj')).trans (hdyadic j hj₀ hjJ)).trans
    apply ENNReal.ofReal_le_ofReal
    calc
      2*(plateScale j)^b ≤ 2*(2*t)^b :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (plateScale_pos _).le hjt' hb) (by norm_num)
      _ = (2*(2:ℝ)^b)*t^b := by rw [Real.mul_rpow (by norm_num) ht.le]; ring
      _ ≤ C*t^b := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ht.le _)

end Falconer

end OAI
