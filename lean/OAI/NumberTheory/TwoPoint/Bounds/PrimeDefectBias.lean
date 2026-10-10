import OAI.NumberTheory.TwoPoint.Bounds.PrimeDefectLimit
import OAI.NumberTheory.TwoPoint.Bounds.RoughShiftBoundary

namespace OAI

/-! Persistent ordinary two-point bias forces finite reciprocal prime-modulus
defect for both factors. This is an elementary consequence of the p² CRT
majorant, with no additional mean-value input. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Topology

lemma shifted_modulus_sum_le {g : ℕ → ℂ} (hg : OneBounded g) (N h : ℕ) :
    (∑ n ∈ range N, ‖g (n + 1 + h)‖) ≤
      (∑ n ∈ range N, ‖g (n + 1)‖) + h := by
  have hleft := sum_range_add (fun n => ‖g (n + 1)‖) h N
  have hright := sum_range_add (fun n => ‖g (n + 1)‖) N h
  have he : (∑ n ∈ range h, ‖g (n + 1)‖) +
      (∑ n ∈ range N, ‖g (n + 1 + h)‖) =
      (∑ n ∈ range N, ‖g (n + 1)‖) +
      (∑ n ∈ range h, ‖g (n + 1 + N)‖) := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hleft.symm.trans
      ((congrArg (fun K => ∑ n ∈ range K, ‖g (n + 1)‖) (Nat.add_comm h N)).trans hright)
  have hn : 0 ≤ ∑ n ∈ range h, ‖g (n + 1)‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have ht : (∑ n ∈ range h, ‖g (n + 1 + N)‖) ≤ (h : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ range h, (1 : ℝ) := sum_le_sum (fun n _ => hg _ (by omega))
      _ = _ := by simp
  linarith

lemma normalized_correlation_le_first_modulus {f g : ℕ → ℂ} (hg : OneBounded g)
    (h N : ℕ) :
    ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ ≤
      (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ) := by
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left (hg _ (by omega)) (norm_nonneg _)).trans_eq (mul_one _)

lemma normalized_correlation_le_second_modulus {f g : ℕ → ℂ} (hf : OneBounded f)
    (hg : OneBounded g) (h N : ℕ) :
    ‖positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)‖ ≤
      (∑ n ∈ range N, ‖g (n + 1)‖) / (N : ℝ) + (h : ℝ) / N := by
  rw [← add_div, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply le_trans _ (shifted_modulus_sum_le hg N h)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hf _ (by omega)) (norm_nonneg _)).trans_eq (one_mul _)

theorem correlation_zero_of_first_modulus_mean_zero {f g : ℕ → ℂ}
    (hg : OneBounded g) (h : ℕ)
    (hz : Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖f (n + 1)‖) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (normalized_correlation_le_first_modulus hg h) hz

theorem correlation_zero_of_second_modulus_mean_zero {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g) (h : ℕ)
    (hz : Tendsto (fun N : ℕ => (∑ n ∈ range N, ‖g (n + 1)‖) / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := hz.add (tendsto_const_div_atTop_nhds_zero_nat (h : ℝ))
  simp only [zero_add] at ht
  exact squeeze_zero (fun _ => norm_nonneg _)
    (normalized_correlation_le_second_modulus hf hg h) ht

theorem persistent_correlation_prime_defects {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf : OneBounded f) (hg : OneBounded g) (h : ℕ)
    (hbias : ¬Tendsto
      (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0)) :
    Summable (primeModulusDefect f) ∧ Summable (primeModulusDefect g) := by
  constructor
  · by_contra hn
    exact hbias (correlation_zero_of_first_modulus_mean_zero hg h
      (mean_modulus_zero_of_not_summable_prime_defect hfm hf hn))
  · by_contra hn
    exact hbias (correlation_zero_of_second_modulus_mean_zero hf hg h
      (mean_modulus_zero_of_not_summable_prime_defect hgm hg hn))

theorem persistent_correlation_one_values {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g) (h : ℕ)
    (hbias : ¬Tendsto
      (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ))
      atTop (𝓝 0)) : f 1 = 1 ∧ g 1 = 1 := by
  have hzero (hz : ∀ n, 0 < n → f n * g (n + h) = 0) : False := by
    apply hbias
    have he : (fun N : ℕ => positivePrefix (fun n => f n * g (n + h)) N / (N : ℂ)) =
        fun _ => 0 := by
      funext N
      unfold positivePrefix
      rw [sum_eq_zero (fun n _ => hz _ (by omega)), zero_div]
    rw [he]
    exact tendsto_const_nhds
  constructor
  · by_contra hn
    exact hzero (fun n hnpos => by rw [hfm.eq_zero_of_one_ne hn n hnpos, zero_mul])
  · by_contra hn
    exact hzero (fun n hnpos => by rw [hgm.eq_zero_of_one_ne hn (n + h) (by omega), mul_zero])

end TwoPointCorrelations

end OAI
