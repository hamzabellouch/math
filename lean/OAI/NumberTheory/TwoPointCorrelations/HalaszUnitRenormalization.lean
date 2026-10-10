import OAI.NumberTheory.TwoPointCorrelations.HalaszPhaseSum
import OAI.NumberTheory.TwoPointCorrelations.HalaszUnitMean

namespace OAI

/-! Elementary near-twist renormalization using the absolute unit correction.
The power-sum error is uniform in the summation cutoff and linear in the twist. -/

namespace TwoPointCorrelations

open Finset

noncomputable def halaszPhaseMean (F : ℕ → ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, F n * halaszPowerPhase t n

noncomputable def halaszUnitMain (F : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ) * ∑ d ∈ Icc 1 N, halaszUnitCorrection F d / (d : ℂ)

lemma halasz_power_phase_mul (t x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    halaszPowerPhase t (x * y) = halaszPowerPhase t x * halaszPowerPhase t y := by
  simp only [halaszPowerPhase, Real.log_mul hx.ne' hy.ne', mul_add,
    Complex.ofReal_add, add_mul, Complex.exp_add]

lemma halasz_phase_factor_norm (t x : ℝ) :
    ‖halaszPowerPhase t x / (1 + (-t : ℂ) * Complex.I)‖ ≤ 1 := by
  have hd : 1 ≤ ‖(1 : ℂ) + (-t : ℂ) * Complex.I‖ := by
    simpa [Complex.mul_re] using Complex.re_le_norm ((1 : ℂ) + (-t : ℂ) * Complex.I)
  rw [norm_div, halasz_power_phase_norm]
  exact (div_le_one (by linarith)).mpr hd

lemma halasz_phase_mean_hyperbola (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    halaszPhaseMean F t N = ∑ d ∈ Icc 1 N,
      halaszUnitCorrection F d * halaszPowerPhase t d *
        ∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m := by
  unfold halaszPhaseMean
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ n.divisorsAntidiagonal,
        halaszUnitCorrection F p.1 * halaszPowerPhase t (p.1 * p.2) := by
      apply sum_congr rfl
      intro n hn
      rw [halasz_unit_correction_divisor_sum F hF hF1 (mem_Icc.mp hn).1, sum_mul,
        Nat.sum_divisorsAntidiagonal (fun a b =>
          halaszUnitCorrection F a * halaszPowerPhase t (a * b))]
      apply sum_congr rfl
      intro d hd
      rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1]
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
        halaszUnitCorrection F d * halaszPowerPhase t (d * m) :=
      (halasz_sum_divisorsAntidiagonal (fun d m =>
        halaszUnitCorrection F d * halaszPowerPhase t (d * m)) N).trans
          (halasz_hyperbola_rows (fun d m =>
            halaszUnitCorrection F d * halaszPowerPhase t (d * m)) N)
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [mul_sum]
      apply sum_congr rfl
      intro m hm
      rw [halasz_power_phase_mul t d m
        (by exact_mod_cast (mem_Icc.mp hd).1) (by exact_mod_cast (mem_Icc.mp hm).1)]
      ring

lemma halasz_phase_main_local (t : ℝ) (N d : ℕ) (hd : 0 < d) :
    halaszPowerPhase t d *
      (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
        (1 + (-t : ℂ) * Complex.I)) =
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * (N : ℂ) / d := by
  by_cases hN : N = 0
  · subst N; simp
  have hdp : 0 < (d : ℝ) := by exact_mod_cast hd
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have he := halasz_power_phase_mul t d ((N : ℝ) / d) hdp (div_pos hNp hdp)
  rw [mul_div_cancel₀ _ hdp.ne'] at he
  push_cast
  rw [he]
  ring

theorem halasz_phase_mean_main_error (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N‖ ≤
      9 * (1 + |t|) * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
  have he : halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N =
      ∑ d ∈ Icc 1 N, halaszUnitCorrection F d * halaszPowerPhase t d *
        ((∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
            (1 + (-t : ℂ) * Complex.I))) := by
    rw [halasz_phase_mean_hyperbola F hF hF1, halaszUnitMain, ← mul_assoc, mul_sum,
      ← sum_sub_distrib]
    apply sum_congr rfl
    intro d hd
    have hh := halasz_phase_main_local t N d (mem_Icc.mp hd).1
    calc
      _ = halaszUnitCorrection F d * halaszPowerPhase t d *
          (∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          halaszUnitCorrection F d *
            ((halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * (N : ℂ) / d) := by ring
      _ = _ := by rw [← hh]; ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d * halaszPowerPhase t d *
        ((∑ m ∈ Icc 1 (N / d), halaszPowerPhase t m) -
          (((N : ℝ) / d : ℝ) * halaszPowerPhase t ((N : ℝ) / d) /
            (1 + (-t : ℂ) * Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ * (9 * (1 + |t|)) := by
      apply sum_le_sum
      intro d hd
      have hh := halasz_power_phase_sum_real t ((N : ℝ) / d) (by positivity)
      rw [Nat.floor_div_natCast, Nat.floor_natCast] at hh
      simpa only [norm_mul, halasz_power_phase_norm, mul_one] using
        mul_le_mul_of_nonneg_left hh (norm_nonneg (halaszUnitCorrection F d))
    _ = _ := by rw [← sum_mul]; ring

/-- A cutoff-uniform renormalization. Only the absolute correction mass is
needed; its near-center saving is supplied by `halasz_near_correction_mean`. -/
theorem halasz_unit_renormalization (F : ℕ → ℂ) (hF : Multiplicative F)
    (hF1 : F 1 = 1) (t : ℝ) (N : ℕ) :
    ‖halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszPhaseMean F 0 N‖ ≤
      18 * (1 + |t|) * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
  have hzero : halaszPowerPhase 0 N / (1 + (-(0 : ℝ) : ℂ) * Complex.I) = 1 := by
    simp [halaszPowerPhase]
  have h0 := halasz_phase_mean_main_error F hF hF1 0 N
  rw [hzero, one_mul] at h0
  norm_num at h0
  have ht := halasz_phase_mean_main_error F hF hF1 t N
  have he : halaszPhaseMean F t N -
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszPhaseMean F 0 N =
      (halaszPhaseMean F t N -
        (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) * halaszUnitMain F N) +
      (halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) *
        (halaszUnitMain F N - halaszPhaseMean F 0 N) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hh : ‖(halaszPowerPhase t N / (1 + (-t : ℂ) * Complex.I)) *
        (halaszUnitMain F N - halaszPhaseMean F 0 N)‖ ≤
      9 * ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := by
    rw [norm_mul, norm_sub_rev]
    exact (mul_le_mul_of_nonneg_right (halasz_phase_factor_norm t N) (norm_nonneg _)).trans
      (by simpa using h0)
  have hmass : 0 ≤ ∑ d ∈ Icc 1 N, ‖halaszUnitCorrection F d‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith [abs_nonneg t]

end TwoPointCorrelations

end OAI
