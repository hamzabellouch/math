import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDampingLimit

namespace OAI

/-! # Uniform control of the regularized quadratic Gaussian coefficient -/

namespace Ostmann

open MeasureTheory Filter
open scoped Topology

noncomputable def quadraticFresnelCoefficient (ε a t : ℝ) : ℂ :=
  ((1 : ℂ) / ((ε : ℂ) + 2 * Complex.I * (a * t : ℝ))) ^ (1 / 2 : ℂ)

 theorem quadraticFresnelCoefficient_norm_le (ε : ℝ) {a t : ℝ}
    (ha : 1 ≤ |a|) (ht : 1 / 2 ≤ t) : ‖quadraticFresnelCoefficient ε a t‖ ≤ 1 := by
  let z : ℂ := (ε : ℂ) + 2 * Complex.I * (a * t : ℝ)
  have ht₀ : 0 ≤ t := by linarith
  have him : z.im = 2 * a * t := by simp [z]; ring
  have hn : 1 ≤ ‖z‖ := by
    have hh := Complex.abs_im_le_norm z
    rw [him, abs_mul, abs_mul, abs_of_nonneg ht₀] at hh
    norm_num at hh
    nlinarith
  have hi : ‖(1 : ℂ) / z‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith : 0 < ‖z‖)).mpr hn
  change ‖((1 : ℂ) / z) ^ (1 / 2 : ℂ)‖ ≤ 1
  have he : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [he, Complex.norm_cpow_real]
  exact Real.rpow_le_one (norm_nonneg _) hi (by norm_num)

 theorem quadraticFresnelCoefficient_continuousAt_zero {a t : ℝ} (hat : a * t ≠ 0) :
    ContinuousAt (fun ε : ℝ => quadraticFresnelCoefficient ε a t) 0 := by
  let z : ℂ := 2 * Complex.I * (a * t : ℝ)
  have hz : z ≠ 0 := by
    dsimp [z]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hat)
  have him : z.im = 2 * a * t := by simp [z]; ring
  have hi : z⁻¹ ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    rw [Complex.inv_im]
    apply div_ne_zero
    · rw [him]
      exact neg_ne_zero.mpr (by
        simpa only [mul_assoc] using (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hat))
    · exact (Complex.normSq_pos.mpr hz).ne'
  have hc : ContinuousAt (fun ε : ℝ => (ε : ℂ) + z) 0 := by fun_prop
  have hc' : ContinuousAt (fun ε : ℝ => ((ε : ℂ) + z)⁻¹) 0 :=
    hc.inv₀ (by simpa using hz)
  have ht : Tendsto (fun ε : ℝ => ((ε : ℂ) + z)⁻¹) (𝓝 0) (𝓝 z⁻¹) := by
    simpa using hc'.tendsto
  have hp := (continuousAt_cpow_const (b := (1 / 2 : ℂ)) hi).tendsto.comp ht
  simpa only [ContinuousAt, Function.comp_def, quadraticFresnelCoefficient, one_div, z, Complex.ofReal_zero, zero_add] using hp

end Ostmann

end OAI
