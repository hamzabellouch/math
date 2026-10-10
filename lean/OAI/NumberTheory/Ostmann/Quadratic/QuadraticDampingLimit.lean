import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticDampedFresnel

namespace OAI

/-! # Removing the Gaussian damping from the quadratic Fourier side -/

namespace Ostmann

open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology

 theorem quadraticGaussianDamping_norm_le {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    ‖quadraticGaussianDamping ε x‖ ≤ 1 := by
  rw [quadraticGaussianDamping, Complex.norm_exp]
  have he : -((Real.pi * ε : ℝ) : ℂ) * (x : ℂ) ^ 2 =
      ((-(Real.pi * ε * x ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.ofReal_re, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (by positivity)

 theorem quadraticGaussianDamping_limit (x : ℝ) :
    Tendsto (fun n : ℕ => quadraticGaussianDamping (1 / ((n : ℝ) + 1)) x)
      atTop (𝓝 1) := by
  have hc : Continuous (fun ε : ℝ => quadraticGaussianDamping ε x) := by
    unfold quadraticGaussianDamping
    fun_prop
  have ht := hc.continuousAt.tendsto.comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [quadraticGaussianDamping, Function.comp_def] using ht

 theorem quadratic_damped_fourier_integral_limit (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      quadraticGaussianDamping (1 / ((n : ℝ) + 1)) x * 𝓕 ρ (a * x ^ 2))
      atTop (𝓝 (∫ x : ℝ, 𝓕 ρ (a * x ^ 2))) := by
  apply tendsto_integral_of_dominated_convergence (fun x : ℝ => ‖𝓕 ρ (a * x ^ 2)‖)
  · intro n
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · unfold quadraticGaussianDamping
      fun_prop
    · exact (𝓕 ρ : 𝓢(ℝ, ℂ)).continuous.comp (by fun_prop)
  · exact (quadraticFourierSquare ρ a ha).integrable.norm
  · intro n
    filter_upwards with x
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right
      (quadraticGaussianDamping_norm_le (by positivity) x) (norm_nonneg _)).trans_eq (one_mul _)
  · filter_upwards with x
    simpa only [one_mul] using (quadraticGaussianDamping_limit x).mul_const (𝓕 ρ (a * x ^ 2))

end Ostmann

end OAI
