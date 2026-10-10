import Mathlib

namespace OAI

/-!
Analytic conclusion of the ordered-matrix construction.
The polynomial/geometric comparison uses
`tendsto_pow_const_div_const_pow_of_one_lt`.
-/

noncomputable section

namespace Problem348

open Filter
open scoped Topology


/-- Exponential decay beats the inverse-polynomial distance parameter. -/
theorem exists_depth_polynomial_decay (c C : ℝ) (hc : 0 < c) :
    ∃ h : ℕ, 1 ≤ h ∧
      (1 / ((386 * (h : ℝ) + 2) ^ 2)) * (1 / ((2 : ℝ) ^ h)) <
        c * Real.rpow (1 / ((386 * (h : ℝ) + 2) ^ 2)) C := by
  obtain ⟨k, hk⟩ := exists_nat_ge C
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt (2 * k)
    (by norm_num : (1 : ℝ) < 2)).const_mul ((388 : ℝ) ^ (2 * k))
  have hev : ∀ᶠ h : ℕ in atTop,
      (388 : ℝ) ^ (2 * k) * ((h : ℝ) ^ (2 * k) / (2 : ℝ) ^ h) < c := by
    exact ht.eventually (gt_mem_nhds (by simpa using hc))
  obtain ⟨h, hh, hsmall⟩ := (eventually_ge_atTop 1 |>.and hev).exists
  refine ⟨h, hh, ?_⟩
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hd : 0 < 386 * (h : ℝ) + 2 := by positivity
  have hd1 : (1 : ℝ) < 386 * (h : ℝ) + 2 := by linarith
  have htwo : 0 < (2 : ℝ) ^ h := by positivity
  have hpoly : (386 * (h : ℝ) + 2) ^ (2 * k) ≤
      (388 : ℝ) ^ (2 * k) * (h : ℝ) ^ (2 * k) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hd.le (by linarith) _
  have hratio : (386 * (h : ℝ) + 2) ^ (2 * k) / (2 : ℝ) ^ h < c := by
    calc
      _ ≤ ((388 : ℝ) ^ (2 * k) * (h : ℝ) ^ (2 * k)) / (2 : ℝ) ^ h :=
        div_le_div_of_nonneg_right hpoly htwo.le
      _ = (388 : ℝ) ^ (2 * k) * ((h : ℝ) ^ (2 * k) / (2 : ℝ) ^ h) := by ring
      _ < c := hsmall
  have hepspos : 0 < 1 / ((386 * (h : ℝ) + 2) ^ 2) := by positivity
  have hepsle : 1 / ((386 * (h : ℝ) + 2) ^ 2) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith
  have hexponent : (1 / ((386 * (h : ℝ) + 2) ^ 2)) ^ k ≤
      Real.rpow (1 / ((386 * (h : ℝ) + 2) ^ 2)) C := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hepspos hepsle hk
  have hsmall' : 1 / ((2 : ℝ) ^ h) <
      c * (1 / ((386 * (h : ℝ) + 2) ^ 2)) ^ k := by
    rw [div_pow, one_pow, ← pow_mul, mul_one_div]
    apply (lt_div_iff₀ (pow_pos hd (2 * k))).2
    simpa [div_eq_mul_inv, mul_comm] using hratio
  calc
    _ ≤ 1 / ((2 : ℝ) ^ h) := by
      exact mul_le_of_le_one_left (by positivity) hepsle
    _ < c * (1 / ((386 * (h : ℝ) + 2) ^ 2)) ^ k := hsmall'
    _ ≤ c * Real.rpow (1 / ((386 * (h : ℝ) + 2) ^ 2)) C :=
      mul_le_mul_of_nonneg_left hexponent hc.le

end Problem348

end

end OAI
