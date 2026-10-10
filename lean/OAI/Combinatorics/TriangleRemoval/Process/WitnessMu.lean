import Mathlib

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators

namespace SharpTerminalLeave

theorem witness_exp_series (x : ℝ) :
    HasSum (fun j : ℕ => x ^ j / (j.factorial : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem three_segment_series (x : ℝ) :
    (∑' h : ℕ, ∑' a : ℕ, ∑' b : ℕ,
      x ^ (h + a + b) /
        ((h.factorial : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ))) = Real.exp (3 * x) := by
  simp_rw [pow_add, ← div_mul_div_comm, tsum_mul_left, tsum_mul_right,
    (witness_exp_series x).tsum_eq]
  simp only [tsum_mul_left, tsum_mul_right, (witness_exp_series x).tsum_eq]
  rw [show (3 : ℝ) * x = x + x + x by ring, Real.exp_add, Real.exp_add]

noncomputable def witnessMu (D : ℝ) : ℝ := Real.log (1 + 2 * D) / (2 * D)

theorem witnessMu_nonneg {D : ℝ} (hD : 0 < D) : 0 ≤ witnessMu D := by
  exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)

theorem witness_length_sum {D : ℝ} (hD : 0 < D) :
    (1 + 2 * D) ^ 3 * (∑' h : ℕ, ∑' a : ℕ, ∑' b : ℕ,
      (8 * D * witnessMu D) ^ (h + a + b) /
        ((h.factorial : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ))) =
      (1 + 2 * D) ^ 15 := by
  rw [three_segment_series]
  have he : 3 * (8 * D * witnessMu D) = 12 * Real.log (1 + 2 * D) := by
    unfold witnessMu
    field_simp
    ring
  rw [he, show (12 : ℝ) = (12 : ℕ) by norm_num, Real.exp_nat_mul,
    Real.exp_log (by linarith : 0 < 1 + 2 * D)]
  rw [← pow_add]

theorem witness_power_bound {D : ℝ} (hD : 1 ≤ D) :
    (1 + 2 * D) ^ 15 / D ^ 50 ≤ (3 : ℝ) ^ 15 / D ^ 35 := by
  have hpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hm : (1 + 2 * D) ^ 15 ≤ (3 * D) ^ 15 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hh := div_le_div_of_nonneg_right hm (le_of_lt (pow_pos hpos 50))
  apply hh.trans_eq
  rw [mul_pow, show 50 = 15 + 35 by norm_num, pow_add]
  field_simp

end SharpTerminalLeave

end

end OAI
