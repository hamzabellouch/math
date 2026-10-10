import OAI.NumberTheory.TwoPoint.Halasz.HalaszSmoothSeries
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSmoothDistance

namespace OAI

/-! Continuity and uniform bounds for the actual smooth Euler series on
the Perron line. Only values at positive integers are bounded. -/

namespace TwoPointCorrelations

open Finset Complex

lemma halasz_distance_nonneg (f : ℕ → ℂ) (hf : OneBounded f) (N : ℕ) (t : ℝ) :
    0 ≤ squaredDistance f (mrtArchimedeanTwist t) N := by
  unfold squaredDistance
  apply sum_nonneg
  intro p hp
  apply div_nonneg _ (Nat.cast_nonneg _)
  have hprime : p.Prime := (mem_filter.mp hp).2
  have hn : ‖f p * star (mrtArchimedeanTwist t p)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, mrtArchimedeanTwist_norm, mul_one] using hf p hprime.pos
  exact sub_nonneg.mpr ((Complex.re_le_norm _).trans hn)

lemma halasz_smooth_line_continuous (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (hbound : OneBounded f) (N : ℕ) :
    Continuous (fun t : ℝ => LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)) := by
  have he (t : ℝ) : LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I) =
      ∏ p ∈ primesUpTo N, (1 - mrtPrimeEulerTerm f t p)⁻¹ := by
    rw [halasz_smooth_LSeries, (mrt_smooth_euler_product f hf1 hf hbound N t).2.tsum_eq]
  simp_rw [he]
  apply continuous_finsetProd
  intro p hp
  apply Continuous.inv₀
  · unfold mrtPrimeEulerTerm mrtArchimedeanTwist
    fun_prop
  · intro t ht
    have hprime : p.Prime := (mem_filter.mp hp).2
    have hn := mrt_prime_euler_norm_lt_one f hbound t hprime
    have heq : mrtPrimeEulerTerm f t p = 1 := (sub_eq_zero.mp ht).symm
    rw [heq, norm_one] at hn
    exact lt_irrefl _ hn

theorem halasz_smooth_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n) → OneBounded f →
      ∀ (N : ℕ), 2 ≤ N → ∀ t : ℝ,
      ‖LSeries (halaszSmoothFunction f N) (1 + (t : ℂ) * I)‖ ≤ C * Real.log N := by
  obtain ⟨C, hC, hb⟩ := mrt_smooth_distance_bound
  refine ⟨C, hC, ?_⟩
  intro f hf1 hf hbound N hN t
  rw [halasz_smooth_LSeries]
  apply (hb f hf1 hf hbound N hN t).trans
  have hn := halasz_distance_nonneg f hbound N t
  have hexp : Real.exp (-squaredDistance f (mrtArchimedeanTwist t) N) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (mul_nonneg hC.le hlog)

end TwoPointCorrelations

end OAI
