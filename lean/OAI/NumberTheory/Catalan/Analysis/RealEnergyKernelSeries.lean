import OAI.NumberTheory.Catalan.Analysis.RealEnergyLogSeries
import OAI.NumberTheory.Catalan.Estimates.RealEnergyChebyshev

namespace OAI

noncomputable section
open Polynomial Set
open scoped ComplexConjugate

namespace InternalCatalan

theorem energy_scaled_pow_re (a : ℝ) (z : ℂ) (k : ℕ) :
    (((a : ℂ) * z) ^ k).re = a ^ k * (z ^ k).re := by
  simp only [mul_pow, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem energy_hasSum_cosine_kernel {r u v : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ =>
      2 * r ^ k * (Chebyshev.T ℝ (k : ℤ)).eval u * (Chebyshev.T ℝ (k : ℤ)).eval v /
        (k : ℝ)) (-realEnergyCosineKernel r u v - Real.log 2) := by
  have hn1 : ‖(r : ℂ) * (realEnergyCirclePoint u * realEnergyCirclePoint v)‖ < 1 := by
    simpa only [Complex.norm_mul, realEnergyCirclePoint_norm hu,
      realEnergyCirclePoint_norm hv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr.1, mul_one] using hr.2
  have hn2 : ‖(r : ℂ) * (realEnergyCirclePoint u * conj (realEnergyCirclePoint v))‖ < 1 := by
    simpa only [Complex.norm_mul, Complex.norm_conj, realEnergyCirclePoint_norm hu,
      realEnergyCirclePoint_norm hv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr.1, mul_one] using hr.2
  have h1 := energy_hasSum_re_power_div hn1
  have h2 := energy_hasSum_re_power_div hn2
  convert h1.add h2 using 1
  · ext k
    rw [energy_scaled_pow_re, energy_scaled_pow_re]
    have hp := realEnergyCirclePoint_pair_pow_re k hu hv
    calc
      _ = r ^ k *
          (((realEnergyCirclePoint u * realEnergyCirclePoint v) ^ k).re +
            ((realEnergyCirclePoint u * conj (realEnergyCirclePoint v)) ^ k).re) / (k : ℝ) := by
        rw [hp]
        ring
      _ = _ := by ring
  · unfold realEnergyCosineKernel
    ring

theorem energy_summable_abs_cosine_kernel {r u v : ℝ}
    (hr : r ∈ Ico (0 : ℝ) 1)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    Summable (fun k : ℕ =>
      |2 * r ^ k * (Chebyshev.T ℝ (k : ℤ)).eval u * (Chebyshev.T ℝ (k : ℤ)).eval v /
        (k : ℝ)|) := (energy_hasSum_cosine_kernel hr hu hv).summable.abs

theorem realEnergy_circle_scaled_chord_sq (x : ℝ) {s : ℝ}
    (hs : s ∈ Icc (-1 : ℝ) 1) :
    ‖(1 : ℂ) - (x : ℂ) * realEnergyCirclePoint s‖ ^ 2 = 1 - 2 * x * s + x ^ 2 := by
  have hsq : Complex.normSq (realEnergyCirclePoint s) = 1 := by
    rw [Complex.normSq_eq_norm_sq, realEnergyCirclePoint_norm hs, one_pow]
  have hre : (realEnergyCirclePoint s).re = s := by simp [realEnergyCirclePoint]
  simp only [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_one,
    Complex.normSq_mul, Complex.normSq_ofReal, hsq, one_mul, mul_one,
    Complex.conj_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hre]
  ring

theorem energy_hasSum_cross_kernel {x s : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun k : ℕ => 2 * x ^ k * (Chebyshev.T ℝ (k : ℤ)).eval s / (k : ℝ))
      (-Real.log (1 - 2 * x * s + x ^ 2)) := by
  have hz : ‖(x : ℂ) * realEnergyCirclePoint s‖ < 1 := by
    simpa only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      realEnergyCirclePoint_norm hs, mul_one] using abs_lt.mpr hx
  have hh := (energy_hasSum_re_power_div hz).mul_left (2 : ℝ)
  have hl : Real.log (1 - 2 * x * s + x ^ 2) =
      2 * Real.log ‖(1 : ℂ) - (x : ℂ) * realEnergyCirclePoint s‖ := by
    rw [← realEnergy_circle_scaled_chord_sq x hs, Real.log_pow]
    norm_num
  convert hh using 1
  · ext k
    rw [energy_scaled_pow_re, realEnergyCirclePoint_pow_re k hs]
    ring
  · rw [hl]
    ring

theorem energy_summable_abs_cross_kernel {x s : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) :
    Summable (fun k : ℕ =>
      |2 * x ^ k * (Chebyshev.T ℝ (k : ℤ)).eval s / (k : ℝ)|) :=
  (energy_hasSum_cross_kernel hx hs).summable.abs

end InternalCatalan

end

end OAI
