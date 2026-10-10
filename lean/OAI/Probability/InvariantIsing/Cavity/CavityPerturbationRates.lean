import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Deriv

namespace OAI

/-! A bounded dimension jump changes the deterministic and Gaussian
perturbation amplitudes by a vanishing amount. -/

noncomputable section
open IsingPerceptron Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_rpow_increment_le {x t p : ℝ} (hx : 0 < x) (ht : 0 ≤ t)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    |(x + t) ^ p - x ^ p| ≤ (p * t) * x ^ (p - 1) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hc := (Real.concaveOn_rpow hp₀ hp₁).slope_le_of_hasDerivAt hx.le
    (show 0 ≤ x + t by positivity) (show x < x + t by linarith)
    (Real.hasDerivAt_rpow_const (Or.inl hx.ne'))
  rw [slope_def_field, add_sub_cancel_left] at hc
  have hd : 0 ≤ (x + t) ^ p - x ^ p :=
    sub_nonneg.mpr (Real.rpow_le_rpow hx.le (by linarith) hp₀)
  rw [abs_of_nonneg hd]
  have h := (div_le_iff₀ ht).mp hc
  nlinarith

lemma cavity_nat_rpow_increment_tendsto (n : ℕ) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p < 1) :
    Tendsto (fun N : ℕ => ((N + n : ℕ) : ℝ) ^ p - (N : ℝ) ^ p) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    simpa only [Real.norm_eq_abs, Nat.cast_add] using
      cavity_rpow_increment_le hN' (Nat.cast_nonneg n) hp₀ hp₁.le
  · have h := (tendsto_nat_rpow_neg (sub_pos.mpr hp₁)).const_mul (p * n)
    simpa only [neg_sub, mul_zero] using h

lemma cavity_deterministic_amplitude_eq {N : ℕ} (hN : 0 < N) :
    N * perturbationScale N = (N : ℝ) ^ (15 / 16 : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  calc
    _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ) := by
      rw [Real.rpow_one]
      rfl
    _ = (N : ℝ) ^ ((1 : ℝ) + (-1 / 16)) := (Real.rpow_add hn _ _).symm
    _ = _ := by norm_num

lemma cavity_covariance_amplitude_eq {N : ℕ} (hN : 0 < N) :
    N * perturbationScale N ^ 2 = (N : ℝ) ^ (7 / 8 : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  change (N : ℝ) * ((N : ℝ) ^ (-1 / 16 : ℝ)) ^ 2 = _
  rw [pow_two, ← mul_assoc]
  calc
    _ = ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-1 / 16 : ℝ)) *
        (N : ℝ) ^ (-1 / 16 : ℝ) := by rw [Real.rpow_one]
    _ = (N : ℝ) ^ ((1 : ℝ) + (-1 / 16) + (-1 / 16)) := by
      rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    _ = _ := by norm_num

theorem cavity_deterministic_amplitude_increment_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N + n) * perturbationScale (N + n) - N * perturbationScale N)
      atTop (𝓝 0) := by
  apply (cavity_nat_rpow_increment_tendsto n (p := 15 / 16) (by norm_num) (by norm_num)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← Nat.cast_add, cavity_deterministic_amplitude_eq (N := N + n) (by omega),
    cavity_deterministic_amplitude_eq (N := N) (by omega)]

theorem cavity_covariance_amplitude_increment_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N + n) * perturbationScale (N + n) ^ 2 -
      N * perturbationScale N ^ 2) atTop (𝓝 0) := by
  apply (cavity_nat_rpow_increment_tendsto n (p := 7 / 8) (by norm_num) (by norm_num)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← Nat.cast_add, cavity_covariance_amplitude_eq (N := N + n) (by omega),
    cavity_covariance_amplitude_eq (N := N) (by omega)]

end InvariantIsing

end

end OAI
