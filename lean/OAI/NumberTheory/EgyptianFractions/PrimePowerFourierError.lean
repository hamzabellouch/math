import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldt
import OAI.NumberTheory.EgyptianFractions.ThreePrimeContinuousFourier

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace Problem337

/-- Removing proper prime powers from a bounded complex-weighted sum costs
exactly at most the difference of the Chebyshev functions. The bound is
uniform in the phase and requires no cancellation hypothesis. -/
theorem norm_mangoldt_sum_sub_prime_sum_le (N : ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ Finset.Icc 1 N, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * f n) -
      ∑ n ∈ Finset.Icc 1 N, (primeLogWeight n : ℂ) * f n‖ ≤
        Chebyshev.psi N - Chebyshev.theta N := by
  rw [← Finset.sum_sub_distrib, ← sum_primePowerLogWeight N]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro n hn
  rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr (primeLogWeight_le_vonMangoldt n))]
  exact mul_le_of_le_one_right
    (sub_nonneg.mpr (primeLogWeight_le_vonMangoldt n)) (hf n hn)

/-- The same removal estimate with the prime sum first. -/
theorem norm_prime_sum_sub_mangoldt_sum_le (N : ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ Finset.Icc 1 N, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.Icc 1 N, (primeLogWeight n : ℂ) * f n) -
      ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * f n‖ ≤
        Chebyshev.psi N - Chebyshev.theta N := by
  rw [norm_sub_rev]
  exact norm_mangoldt_sum_sub_prime_sum_le N f hf

/-- A pointwise prime-sum estimate follows from the corresponding Mangoldt
estimate with the elementary prime-power error added. -/
theorem norm_prime_sum_le_mangoldt_sum_add (N : ℕ) (f : ℕ → ℂ)
    (hf : ∀ n ∈ Finset.Icc 1 N, ‖f n‖ ≤ 1) :
    ‖∑ n ∈ Finset.Icc 1 N, (primeLogWeight n : ℂ) * f n‖ ≤
      ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * f n‖ +
        (Chebyshev.psi N - Chebyshev.theta N) := by
  have h := norm_prime_sum_sub_mangoldt_sum_le N f hf
  have ht := norm_add_le
    ((∑ n ∈ Finset.Icc 1 N, (primeLogWeight n : ℂ) * f n) -
      ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * f n)
    (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * f n)
  rw [sub_add_cancel] at ht
  linarith

/-- Every fixed logarithmic loss is negligible compared with the power saving
in the elementary prime-power estimate. -/
theorem prime_power_error_mul_log_isLittleO (B : ℕ) :
    (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) * Real.log x ^ B)
      =o[atTop] (fun x : ℝ => x) := by
  have hlog : (fun x : ℝ => Real.log x ^ B) =o[atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    simpa only [Real.rpow_natCast] using
      isLittleO_log_rpow_rpow_atTop (B : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have h := hlog.mul_isBigO Chebyshev.isBigO_psi_sub_theta_sqrt
  apply h.congr'
  · exact Eventually.of_forall (fun x => by simp only [Pi.sub_apply]; ring)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
    norm_num

/-- A scalar form suited to logarithmic minor-arc budgets. The onset depends
only on the desired saving and error, not on any Fourier frequency. -/
theorem eventually_prime_power_error_le_log_budget (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Chebyshev.psi N - Chebyshev.theta N ≤
        ε * ((N : ℝ) / Real.log (N : ℝ) ^ B) := by
  have he := ((prime_power_error_mul_log_isLittleO B).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).bound hε
  filter_upwards [he, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlog : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hpow : 0 < Real.log (N : ℝ) ^ B := pow_pos hlog B
  simp only [Function.comp_apply, Real.norm_eq_abs] at hN
  rw [abs_of_nonneg hN0] at hN
  have hbound := (le_abs_self
    ((Chebyshev.psi N - Chebyshev.theta N) * Real.log (N : ℝ) ^ B)).trans hN
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hpow).2 hbound

/-- Uniform removal of proper prime powers at any fixed logarithmic saving.
In particular the phase may be chosen after the summation length. -/
theorem eventually_norm_mangoldt_sum_sub_prime_sum_le_log_budget
    (B : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : ℕ → ℂ,
      (∀ n ∈ Finset.Icc 1 N, ‖f n‖ ≤ 1) →
      ‖(∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) * f n) -
        ∑ n ∈ Finset.Icc 1 N, (primeLogWeight n : ℂ) * f n‖ ≤
          ε * ((N : ℝ) / Real.log (N : ℝ) ^ B) := by
  filter_upwards [eventually_prime_power_error_le_log_budget B ε hε] with N hN
  intro f hf
  exact (norm_mangoldt_sum_sub_prime_sum_le N f hf).trans hN

namespace ThreePrimeContinuousFourier

/-- Specialization to the canonical continuous Fourier phase. -/
theorem norm_mangoldt_fourier_sub_prime_fourier_le (N : ℕ) (x : ℝ) :
    ‖(∑ n ∈ Finset.Icc 1 N,
        (ArithmeticFunction.vonMangoldt n : ℂ) * phase (n : ℤ) x) -
      ∑ n ∈ Finset.Icc 1 N, (primeLogWeight n : ℂ) * phase (n : ℤ) x‖ ≤
        Chebyshev.psi N - Chebyshev.theta N := by
  exact norm_mangoldt_sum_sub_prime_sum_le N (fun n => phase (n : ℤ) x)
    (fun n _ => (norm_phase (n : ℤ) x).le)

end ThreePrimeContinuousFourier
end Problem337

end

end OAI
