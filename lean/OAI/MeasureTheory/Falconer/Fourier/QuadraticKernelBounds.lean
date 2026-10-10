import OAI.MeasureTheory.Falconer.Fourier.QuadraticGaussianPairing
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace OAI

namespace PlanarFalconer
open MeasureTheory

 theorem quadratic_exponential_norm_le_one {a : ℂ} (ha : 0 ≤ a.re) (s : ℝ) :
    ‖Complex.exp (-((s:ℂ)^2)/(4*a))‖ ≤ 1 := by
  have he : -((s:ℂ)^2)/(4*a) = ((-s^2/4:ℝ):ℂ)*a⁻¹ := by
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he,Complex.norm_exp,Complex.re_ofReal_mul]
  apply Real.exp_le_one_iff.mpr
  have hi : 0 ≤ a⁻¹.re := by rw [Complex.inv_re]; exact div_nonneg ha (Complex.normSq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) (by norm_num)) hi

 theorem quadraticFourierKernel_norm_bound {a : ℂ} (ha : 0 ≤ a.re)
    {b : ℝ} (hb : 0 < b) (hn : b ≤ ‖a‖) (ξ : ℝ) :
    ‖quadraticFourierKernel a ξ‖ ≤ (Real.pi/b)^(1/2:ℝ) := by
  unfold quadraticFourierKernel
  rw [norm_mul]
  have hpow : ‖((Real.pi:ℂ)/a)^(1/2:ℂ)‖ = (Real.pi/‖a‖)^(1/2:ℝ) := by
    convert Complex.norm_cpow_real ((Real.pi:ℂ)/a) (1/2:ℝ) using 1 <;>
      simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hpow]
  calc
    _ ≤ (Real.pi/‖a‖)^(1/2:ℝ)*1 := mul_le_mul_of_nonneg_left
      (quadratic_exponential_norm_le_one ha _) (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left Real.pi_pos.le hb hn) (by norm_num)

 theorem quadraticFourierKernel_damped_bound {b : ℝ} (hb : 0 < b) {ε : ℝ}
    (hε : 0 ≤ ε) (ξ : ℝ) :
    ‖quadraticFourierKernel ((ε:ℂ)+(b:ℂ)*Complex.I) ξ‖ ≤ (Real.pi/b)^(1/2:ℝ) := by
  apply quadraticFourierKernel_norm_bound (by simpa using hε) hb
  have hh := Complex.abs_im_le_norm ((ε:ℂ)+(b:ℂ)*Complex.I)
  simpa [abs_of_pos hb] using hh

end PlanarFalconer

end OAI
