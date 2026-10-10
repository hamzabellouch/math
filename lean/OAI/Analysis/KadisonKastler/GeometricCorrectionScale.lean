import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

namespace OAI

/-! # The summable error scale for multiplication correction -/

namespace KadisonKastler

open Filter Topology

noncomputable section

def correctionScale (q : ℝ) (n : ℕ) : ℝ := q * (1 / 2 : ℝ) ^ n

@[simp] theorem correctionScale_zero (q : ℝ) : correctionScale q 0 = q := by
  simp [correctionScale]

theorem correctionScale_succ (q : ℝ) (n : ℕ) :
    correctionScale q (n + 1) = correctionScale q n / 2 := by
  simp only [correctionScale, pow_succ]
  ring

theorem correctionScale_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ correctionScale q n := by
  unfold correctionScale
  positivity

theorem correctionScale_le {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : correctionScale q n ≤ q := by
  exact (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)) hq).trans_eq
    (mul_one q)

theorem correctionScale_summable (q : ℝ) : Summable (correctionScale q) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left q

theorem correctionScale_tsum (q : ℝ) : ∑' n, correctionScale q n = 2 * q := by
  change (∑' n : ℕ, q * (1/2 : ℝ)^n) = 2*q
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · ring
  · norm_num

theorem correctionScale_tendsto (q : ℝ) : Tendsto (correctionScale q) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => q * (1/2 : ℝ)^n) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_const_nhds.mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))

theorem correctionScale_partial_sum {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ∑ i ∈ Finset.range n, correctionScale q i ≤ 2 * q := by
  rw [← correctionScale_tsum]
  exact (correctionScale_summable q).sum_le_tsum _
    (fun i _ => correctionScale_nonneg hq i)

end

end KadisonKastler

end OAI
