import Mathlib.Analysis.Fourier.AddCircle

namespace OAI

open scoped BigOperators
open MeasureTheory Complex

namespace Ostmann

noncomputable def trigPoly (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * Complex.exp (2 * Real.pi * Complex.I * n * t)

noncomputable def trigPolyDeriv (N : ℕ) (a : ℕ → ℂ) : ℝ → ℂ :=
  trigPoly N (fun n => a n * (2 * Real.pi * Complex.I * n))

private noncomputable def circlePoly (N : ℕ) (a : ℕ → ℂ) : C(UnitAddCircle, ℂ) :=
  ∑ n ∈ Finset.range N, a n • fourier (n : ℤ)

private theorem circlePoly_coe (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    circlePoly N a (t : UnitAddCircle) = trigPoly N a t := by
  simp only [circlePoly, trigPoly, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, fourier_coe_apply, Int.cast_natCast, Complex.ofReal_one, div_one]

private theorem circlePoly_integral (N : ℕ) (a : ℕ → ℂ) :
    (∫ t : UnitAddCircle, ‖circlePoly N a t‖ ^ 2) =
      ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have hon : Orthonormal ℂ (fun n : ℕ => @fourierLp 1 inferInstance 2 inferInstance (n : ℤ)) :=
    orthonormal_fourier.comp _ Nat.cast_injective
  have h := ContinuousMap.inner_toLp (μ := AddCircle.haarAddCircle)
    (circlePoly N a) (circlePoly N a)
  simp only [circlePoly, map_sum, map_smul] at h
  rw [hon.inner_sum] at h
  change (∑ i ∈ Finset.range N, star (a i) * a i) =
    ∫ t : UnitAddCircle, circlePoly N a t * star (circlePoly N a t)
      ∂AddCircle.haarAddCircle at h
  simp only [Complex.star_def, Complex.conj_mul', Complex.mul_conj',
    ← Complex.ofReal_pow, ← Complex.ofReal_sum, integral_complex_ofReal] at h
  have hr := Complex.ofReal_injective h
  simpa [Complex.normSq_eq_norm_sq, AddCircle.integral_haarAddCircle] using hr.symm

theorem trigPoly_parseval (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖trigPoly N a t‖ ^ 2) =
      ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have h := UnitAddCircle.intervalIntegral_preimage 0
    (fun t => ‖circlePoly N a t‖ ^ 2)
  simpa only [zero_add, circlePoly_coe, circlePoly_integral] using h

theorem trigPoly_hasDerivAt (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (trigPoly N a) (trigPolyDeriv N a t) t := by
  have h := HasDerivAt.sum (u := Finset.range N)
    (fun (n : ℕ) _ => (hasDerivAt_fourier 1 (n : ℤ) t).const_mul (a n))
  convert h using 1
  · ext x
    simp only [trigPoly, Finset.sum_apply, fourier_coe_apply, Int.cast_natCast,
      Complex.ofReal_one, div_one]
  · simp only [trigPolyDeriv, trigPoly, fourier_coe_apply, Int.cast_natCast,
      Complex.ofReal_one, div_one, mul_assoc]

theorem trigPoly_continuous (N : ℕ) (a : ℕ → ℂ) : Continuous (trigPoly N a) :=
  continuous_iff_continuousAt.mpr fun t => (trigPoly_hasDerivAt N a t).continuousAt

theorem trigPolyDeriv_continuous (N : ℕ) (a : ℕ → ℂ) : Continuous (trigPolyDeriv N a) :=
  trigPoly_continuous N _

theorem trigPoly_parseval_interval (N : ℕ) (a : ℕ → ℂ) (b : ℝ) :
    (∫ t in b..b + 1, ‖trigPoly N a t‖ ^ 2) =
      ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have h := UnitAddCircle.intervalIntegral_preimage b
    (fun t => ‖circlePoly N a t‖ ^ 2)
  simpa only [circlePoly_coe, circlePoly_integral] using h

theorem trigPoly_parseval_two (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..2, ‖trigPoly N a t‖ ^ 2) =
      2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have hc : Continuous (fun t => ‖trigPoly N a t‖ ^ 2) :=
    (trigPoly_continuous N a).norm.pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 2)]
  rw [trigPoly_parseval]
  have h := trigPoly_parseval_interval N a 1
  norm_num at h
  rw [h]
  ring

theorem trigPolyDeriv_energy_le (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..1, ‖trigPolyDeriv N a t‖ ^ 2) ≤
      (2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  rw [trigPolyDeriv, trigPoly_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hc : ‖(2 * Real.pi * Complex.I * n : ℂ)‖ ≤ 2 * Real.pi * N := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, Complex.norm_natCast, mul_one]
    gcongr
    exact_mod_cast (Finset.mem_range.mp hn).le
  have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc 2)
    (sq_nonneg ‖a n‖)
  simpa only [norm_mul, mul_pow, mul_comm] using hb

theorem trigPolyDeriv_energy_two_le (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..2, ‖trigPolyDeriv N a t‖ ^ 2) ≤
      2 * (2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have h := trigPolyDeriv_energy_le N a
  rw [trigPolyDeriv, trigPoly_parseval] at h
  rw [trigPolyDeriv, trigPoly_parseval_two]
  nlinarith

theorem trigPoly_deriv_energy_le_two (N : ℕ) (a : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..2, ‖trigPolyDeriv N a t‖ ^ 2) ≤
      (2 * Real.pi * N) ^ 2 * (2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2) := by
  simpa only [mul_left_comm, mul_assoc] using trigPolyDeriv_energy_two_le N a

end Ostmann

end OAI
