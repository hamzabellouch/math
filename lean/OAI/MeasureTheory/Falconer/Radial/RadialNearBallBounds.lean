import OAI.MeasureTheory.Falconer.Incidence.RadialBlockRadius
import OAI.MeasureTheory.Falconer.Geometry.DyadicScaleBallBounds

namespace OAI

/-! # The original pin law controls the concrete near-parent deletion -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem radial_near_ball_bound (hd : 2 ≤ d) (ν : Measure (Space d))
    [IsProbabilityMeasure ν] (N J : ℕ) {ε : ℝ}
    (hball : ∀ x : Space d, ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
      ν (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^((d:ℝ)-1)))
    (hr1 : 8*(d:ℝ)/(2:ℝ)^(radialBlockSize N J) ≤ 1) (x : Space d) :
    ν (ball x (8*(d:ℝ)/(2:ℝ)^(radialBlockSize N J))) ≤
      ENNReal.ofReal ((16*(d:ℝ))^((d:ℝ)-1)*
        ((2:ℝ)^N)^(-(((d:ℝ)-1)/((J:ℝ)+2)-ε))) := by
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 ≤ (d:ℝ)-1 := by linarith
  have hR : 0 < (2:ℝ)^N := by positivity
  have hlo : ((2:ℝ)^N)⁻¹ ≤ 8*(d:ℝ)/(2:ℝ)^(radialBlockSize N J) := by
    have hh : ((2:ℝ)^N)⁻¹ ≤ ((2:ℝ)^(radialBlockSize N J))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (Nat.div_le_self N (J+2)))
    apply hh.trans
    have hb : (1:ℝ) ≤ 8*(d:ℝ) := by linarith
    simpa only [one_mul,div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hb (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2^(radialBlockSize N J)))
  apply (hball x _ hlo hr1).trans
  apply ENNReal.ofReal_le_ofReal
  have hb := radial_block_radius_bound (A := 1) (by norm_num) d N J
  simp only [mul_one] at hb
  calc
    _ ≤ ((2:ℝ)^N)^ε*((16*(d:ℝ))*((2:ℝ)^N)^(-1/((J:ℝ)+2)))^((d:ℝ)-1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hs) (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hR.le]
      rw [show ((2:ℝ)^N)^ε*((16*(d:ℝ))^((d:ℝ)-1)*
        ((2:ℝ)^N)^((-1/((J:ℝ)+2))*((d:ℝ)-1))) =
        (16*(d:ℝ))^((d:ℝ)-1)*(((2:ℝ)^N)^ε*
          ((2:ℝ)^N)^((-1/((J:ℝ)+2))*((d:ℝ)-1))) by ring,
        ← Real.rpow_add hR]
      congr 2
      ring

end Falconer

end OAI
