import Mathlib

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

/-- Geometric cancellation on the complex unit circle. -/
theorem norm_geometric_sum_le_two_div {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (N : ℕ) : ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hz]

/-- The elementary peak bound for a geometric kernel. -/
theorem norm_geometric_sum_le_card {z : ℂ} (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ (N : ℝ) := by
  calc
    ‖∑ j ∈ Finset.range N, z ^ j‖ ≤ ∑ j ∈ Finset.range N, ‖z ^ j‖ := norm_sum_le _ _
    _ = (N : ℝ) := by simp [norm_pow, hz]

/-- Squared cancellation with the usual Fejer normalization. -/
theorem geometric_fejer_le {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    {N : ℕ} (hN : 0 < N) :
    ‖∑ j ∈ Finset.range N, z ^ j‖ ^ 2 / (N : ℝ) ≤
      4 / ((N : ℝ) * ‖z - 1‖ ^ 2) := by
  have hden : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.mpr hne)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := norm_geometric_sum_le_two_div hz hne N
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  calc
    ‖∑ j ∈ Finset.range N, z ^ j‖ ^ 2 / (N : ℝ) ≤
        (2 / ‖z - 1‖) ^ 2 / (N : ℝ) := div_le_div_of_nonneg_right hs2 hNR.le
    _ = 4 / ((N : ℝ) * ‖z - 1‖ ^ 2) := by field_simp; ring

/-- The chord distance for a phase of period one. -/
theorem norm_exp_phase_sub_one (x : ℝ) :
    ‖Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) - 1‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * x / 2 = Real.pi * x := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Geometric cancellation expressed directly in terms of the phase sine. -/
theorem norm_geometric_phase_sum_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
  have habs : 0 < |Real.sin (Real.pi * x)| := abs_pos.2 hx
  have hne : Complex.exp (Complex.I * (2 * Real.pi * x : ℝ)) ≠ 1 := by
    intro h
    have hn := norm_exp_phase_sub_one x
    rw [h, sub_self, norm_zero] at hn
    linarith
  have hbound := norm_geometric_sum_le_two_div
    (Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)) hne N
  rw [norm_exp_phase_sub_one] at hbound
  convert hbound using 1
  field_simp

/-- Uniform lower bound for the sine away from both ends of a period. -/
theorem sin_pi_mul_lower_on_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) :
    2 * δ ≤ Real.sin (Real.pi * x) := by
  have hx0 : 0 ≤ x := le_trans hδ.le hleft
  have hx1 : 0 ≤ 1 - x := by linarith
  by_cases hx : x ≤ 1 / 2
  · have hs := Real.mul_le_sin (x := Real.pi * x)
      (mul_nonneg Real.pi_pos.le hx0) (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * x) = 2 * x := by field_simp
    rw [heq] at hs
    linarith
  · have hs := Real.mul_le_sin (x := Real.pi * (1 - x))
      (mul_nonneg Real.pi_pos.le hx1)
      (by nlinarith [Real.pi_pos])
    have heq : 2 / Real.pi * (Real.pi * (1 - x)) = 2 * (1 - x) := by field_simp
    rw [heq, show Real.pi * (1 - x) = Real.pi - Real.pi * x by ring,
      Real.sin_pi_sub] at hs
    linarith

/-- A phase at distance at least `δ` from the ends gives a uniform kernel bound. -/
theorem norm_geometric_phase_sum_le_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ≤
      1 / (2 * δ) := by
  have hs := sin_pi_mul_lower_on_middle hδ hleft hright
  have hspos : 0 < Real.sin (Real.pi * x) := by linarith
  calc
    _ ≤ 1 / |Real.sin (Real.pi * x)| := norm_geometric_phase_sum_le hspos.ne' N
    _ = 1 / Real.sin (Real.pi * x) := by rw [abs_of_pos hspos]
    _ ≤ 1 / (2 * δ) := one_div_le_one_div_of_le (by positivity) hs

/-- Fejer leakage at phase distance at least `δ` from zero modulo one. -/
theorem geometric_phase_fejer_le_middle {δ x : ℝ} (hδ : 0 < δ)
    (hleft : δ ≤ x) (hright : x ≤ 1 - δ) {N : ℕ} (hN : 0 < N) :
    ‖∑ j ∈ Finset.range N, (Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))) ^ j‖ ^ 2 /
      (N : ℝ) ≤ 1 / (4 * (N : ℝ) * δ ^ 2) := by
  have hs := norm_geometric_phase_sum_le_middle hδ hleft hright N
  have hs2 := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (1 / (2 * δ)) ^ 2 / (N : ℝ) := div_le_div_of_nonneg_right hs2 hNR.le
    _ = 1 / (4 * (N : ℝ) * δ ^ 2) := by field_simp; ring

/-- The standard cyclic character is the period-one phase at its normalized value. -/
theorem stdAddChar_eq_normalized_phase {p : ℕ} [NeZero p] (a : ZMod p) :
    ZMod.stdAddChar a =
      Complex.exp (Complex.I * (2 * Real.pi * ((a.val : ℝ) / (p : ℝ)) : ℝ)) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  congr 1
  push_cast
  ring

/-- Standard-character cancellation on an interval of consecutive integer multiples. -/
theorem norm_stdAddChar_range_sum_le {p : ℕ} [NeZero p] (a : ZMod p)
    (ha : a ≠ 0) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, ZMod.stdAddChar ((j : ZMod p) * a)‖ ≤
      2 / ‖ZMod.stdAddChar a - 1‖ := by
  have hnorm : ‖ZMod.stdAddChar a‖ = 1 := Circle.norm_coe _
  have hne : ZMod.stdAddChar a ≠ 1 := by
    intro h
    apply ha
    apply ZMod.injective_stdAddChar
    simpa using h
  have hpow : ∀ j : ℕ, ZMod.stdAddChar ((j : ZMod p) * a) = (ZMod.stdAddChar a) ^ j := by
    intro j
    simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j a
  simpa only [hpow] using norm_geometric_sum_le_two_div hnorm hne N

/-- The cyclic-character version ready for interval smoothing. -/
theorem norm_stdAddChar_range_sum_le_middle {p : ℕ} [NeZero p] (a : ZMod p)
    {δ : ℝ} (hδ : 0 < δ) (hleft : δ ≤ (a.val : ℝ) / p)
    (hright : (a.val : ℝ) / p ≤ 1 - δ) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, ZMod.stdAddChar ((j : ZMod p) * a)‖ ≤ 1 / (2 * δ) := by
  have hpow : ∀ j : ℕ, ZMod.stdAddChar ((j : ZMod p) * a) = (ZMod.stdAddChar a) ^ j := by
    intro j
    simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j a
  simp_rw [hpow, stdAddChar_eq_normalized_phase]
  exact norm_geometric_phase_sum_le_middle hδ hleft hright N

/-- Squared cyclic kernel leakage, normalized to have total mass one. -/
theorem stdAddChar_fejer_le_middle {p : ℕ} [NeZero p] (a : ZMod p)
    {δ : ℝ} (hδ : 0 < δ) (hleft : δ ≤ (a.val : ℝ) / p)
    (hright : (a.val : ℝ) / p ≤ 1 - δ) {N : ℕ} (hN : 0 < N) :
    ‖∑ j ∈ Finset.range N, ZMod.stdAddChar ((j : ZMod p) * a)‖ ^ 2 / (N : ℝ) ≤
      1 / (4 * (N : ℝ) * δ ^ 2) := by
  have hpow : ∀ j : ℕ, ZMod.stdAddChar ((j : ZMod p) * a) = (ZMod.stdAddChar a) ^ j := by
    intro j
    simpa only [nsmul_eq_mul] using ZMod.stdAddChar.map_nsmul_eq_pow j a
  simp_rw [hpow, stdAddChar_eq_normalized_phase]
  exact geometric_phase_fejer_le_middle hδ hleft hright hN

end Problem337

end

end OAI
