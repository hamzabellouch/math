import OAI.MeasureTheory.Falconer.Shells.HighShellNormalization
import OAI.MeasureTheory.Falconer.Shells.ShellMultipliers

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem high_shell_radial_inverse {v r : ℝ} (hr : (2:ℝ)^(v-1) ≤ r) (j : ℕ) :
    ‖((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ)‖ ≤ (2:ℝ)^j := by
  have hp : 0 < r := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hr
  have he : (2:ℝ)^(v-1) = (2:ℝ)^v/2 := by rw [Real.rpow_sub (by norm_num)]; norm_num
  have hi : (r/(2:ℝ)^v)⁻¹ ≤ 2 := by
    rw [inv_div,div_le_iff₀ hp]
    rw [he] at hr
    linarith
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (by positivity) hi j

theorem high_shell_radial_sqrt {a v r : ℝ}
    (hr : r ∈ Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) :
    ‖(((r*(2:ℝ)^(-a))^(1/2:ℝ):ℝ):ℂ)‖ ≤ Real.sqrt (2*(2:ℝ)^(v-a)) := by
  have hp : 0 ≤ r := (Real.rpow_pos_of_pos (by norm_num) _).le.trans hr.1
  have he : (2:ℝ)^(v+1)*(2:ℝ)^(-a) = 2*(2:ℝ)^(v-a) := by
    rw [Real.rpow_add (by norm_num),Real.rpow_one]
    have hh : (2:ℝ)^v*(2:ℝ)^(-a) = (2:ℝ)^(v-a) := by
      rw [← Real.rpow_add (by norm_num)]; rfl
    calc
      _ = 2*((2:ℝ)^v*(2:ℝ)^(-a)) := by ring
      _ = _ := by rw [hh]
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity),← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt ((mul_le_mul_of_nonneg_right hr.2 (by positivity)).trans_eq he)

end PlanarFalconer

end OAI
