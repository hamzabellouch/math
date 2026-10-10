import Mathlib
import OAI.Combinatorics.KMedian.Analysis.FiniteAverages
import OAI.Combinatorics.KMedian.Analysis.TaylorExpansion
import OAI.Combinatorics.KMedian.Analysis.PolynomialBounds
import OAI.Combinatorics.KMedian.Analysis.TaylorBounds
import OAI.Combinatorics.KMedian.Analysis.ScalarCertificates

namespace OAI

section
section
namespace MetricKMedian.Certificates

open Analytic

theorem pSeries_eq (X : ℝ) : pSeries X = pTaylor 13 (1 - X) := by
  norm_num [pSeries, pTaylor, Finset.sum_range_succ, Nat.factorial]
  ring

theorem aSeries_eq (X : ℝ) : aSeries X = aTaylor 13 (1 - X) := by
  norm_num [aSeries, aTaylor, Finset.sum_range_succ, Nat.factorial]
  ring

theorem p_approximation {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p (1 - x) - P x| ≤ 3 / 400000 := by
  have hX0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hX1 : 1 - x ≤ 1 := by linarith
  have hlo := p_approx_lower hX0 hX1
  have hhi := p_approx_upper hX0 hX1
  rw [pSeries_eq] at hlo hhi
  have hex := P_taylor_error hx0 hx1
  rw [abs_le] at hex ⊢
  simp only [sub_sub_cancel] at hlo hhi
  dsimp only [taylorError] at hex
  constructor <;> linarith

theorem a_approximation {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |v (1 - x) - A x| ≤ 3 / 200000 := by
  have hX0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hX1 : 1 - x ≤ 1 := by linarith
  have hlo := a_approx_lower hX0 hX1
  have hhi := a_approx_upper hX0 hX1
  rw [aSeries_eq] at hlo hhi
  have hex := A_taylor_error hx0 hx1
  rw [abs_le] at hex ⊢
  simp only [sub_sub_cancel] at hlo hhi
  dsimp only [taylorError] at hex
  constructor <;> linarith

theorem k_envelope {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    FiniteComparison.kZero (P x) ≤ k (1 - x) := by
  have hX0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
  have hX1 : 1 - x ≤ 1 := by linarith
  have hk0 := k_lower hX0 hX1
  have hk1 := k_upper hX0 hX1
  have ht := Tk_lower hX0 hX1
  have hp := (abs_le.mp (p_approximation hx0 hx1)).1
  have hP := P_le_half hx0
  have hs0 := Real.sqrt_nonneg (1 - P x)
  have hs : (Real.sqrt (1 - P x)) ^ 2 = 1 - P x := Real.sq_sqrt (by linarith)
  have hmul := mul_le_mul_of_nonneg_right (show P x ≤ p (1-x) + 3/400000 by linarith)
    (sq_nonneg (1 + k (1-x)))
  dsimp only [Tk] at ht
  have hsq : (1 - k (1-x)) ^ 2 ≤ (Real.sqrt (1-P x) * (1+k (1-x))) ^ 2 := by
    rw [mul_pow, hs]
    nlinarith only [ht, hmul]
  have hlin : 1-k (1-x) ≤ Real.sqrt (1-P x) * (1+k (1-x)) := by
    have hright : 0 ≤ Real.sqrt (1-P x) * (1+k (1-x)) := mul_nonneg hs0 (by linarith)
    nlinarith only [hsq, hright]
  unfold FiniteComparison.kZero
  apply (div_le_iff₀ (by linarith : 0 < 1 + Real.sqrt (1 - P x))).mpr
  nlinarith only [hlin]

end MetricKMedian.Certificates


end
end

end OAI
