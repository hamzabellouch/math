import Mathlib

namespace OAI

noncomputable section

namespace Problem315.SliceBounds

theorem product_ge_sum_sub_one {q r : ℝ} (hq : 1 ≤ q) (hr : 1 ≤ r) :
    q + r - 1 ≤ q * r := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hr)]

def equalityProbability (N q r : ℝ) : ℝ :=
  (q * (q - 1) + r * (r - 1)) / (N * (N - 1))

theorem equalityProbability_pos {N q r : ℝ}
    (hN : 3 ≤ N) (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    0 < equalityProbability N q r := by
  unfold equalityProbability
  apply div_pos
  · have hq0 : 0 ≤ q - 1 := sub_nonneg.mpr hq
    have hr0 : 0 ≤ r - 1 := sub_nonneg.mpr hr
    have hqprod := mul_nonneg hq0 hq0
    have hrprod := mul_nonneg hr0 hr0
    nlinarith
  · exact mul_pos (by linarith) (by linarith)

theorem equalityProbability_complement {N q r : ℝ}
    (hN : 1 < N) (hsum : q + r = N) :
    1 - equalityProbability N q r = 2 * q * r / (N * (N - 1)) := by
  have hN0 : N ≠ 0 := ne_of_gt (lt_trans (by norm_num) hN)
  have hN1 : N - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hN)
  unfold equalityProbability
  field_simp
  nlinarith [sq_nonneg (q + r - N)]

theorem linear_numerator_identity {N q r : ℝ}
    (hN : 1 < N) (hsum : q + r = N) :
    N * (N - 2) * equalityProbability N q r - (2 * q - N) ^ 2 =
      2 * N / (N - 1) * (q * r - (N - 1)) := by
  have hN0 : N ≠ 0 := ne_of_gt (lt_trans (by norm_num) hN)
  have hN1 : N - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hN)
  unfold equalityProbability
  rw [← hsum] at *
  field_simp
  ring

theorem linear_eigenvalue_le {N q r : ℝ}
    (hN : 3 ≤ N) (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (2 * q - N) ^ 2 / (2 * (N - 2) * equalityProbability N q r) ≤ N / 2 := by
  have hp := equalityProbability_pos hN hq hr hsum
  have hden : 0 < 2 * (N - 2) * equalityProbability N q r :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hp
  apply (div_le_iff₀ hden).2
  have hid := linear_numerator_identity (by linarith : 1 < N) hsum
  have hqr : 0 ≤ q * r - (N - 1) := by
    have := product_ge_sum_sub_one hq hr
    linarith
  have hquot : 0 ≤ 2 * N / (N - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hnonneg := mul_nonneg hquot hqr
  nlinarith

theorem quadratic_eigenvalue_le {N μ : ℝ} (hN : 4 ≤ N)
    (htrace : (N * (N - 1) / 2 - N) * μ ≤ N * (N - 1) / 2) :
    μ ≤ N - 1 := by
  have hNpos : 0 < N := by linarith
  have hcoef : 0 < N * (N - 3) / 2 :=
    div_pos (mul_pos hNpos (by linarith)) (by norm_num)
  have hbound : N * (N - 1) / 2 ≤ (N * (N - 3) / 2) * (N - 1) := by
    have hprod := mul_nonneg (by linarith : 0 ≤ N - 4) (by linarith : 0 ≤ N - 1)
    have := mul_nonneg (le_of_lt hNpos) hprod
    nlinarith
  have htrace' : (N * (N - 3) / 2) * μ ≤ N * (N - 1) / 2 := by
    nlinarith [htrace]
  exact (mul_le_mul_iff_right₀ hcoef).mp (htrace'.trans hbound)

theorem disjoint_plane_bound {ρ x y : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    -(x ^ 2 + y ^ 2) * (1 - ρ ^ 2) ≤
      2 * x * y * ρ * (1 - ρ ^ 2) := by
  have hbase : 0 ≤ x ^ 2 + y ^ 2 + 2 * x * y * ρ := by
    have h1 := mul_nonneg hρ0 (sq_nonneg (x + y))
    have h2 := mul_nonneg (sub_nonneg.mpr hρ1) (add_nonneg (sq_nonneg x) (sq_nonneg y))
    nlinarith
  have hfactor : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have := mul_nonneg hbase hfactor
  nlinarith

end Problem315.SliceBounds

end

end OAI
