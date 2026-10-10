import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Numerical estimates for the finite sparsest-cut graph

These are the final completeness and soundness inequalities in Section 7 of
*Constant-factor hardness of uniform sparsest cut* by OpenAI.
-/

namespace UniformSparsestCut

/-- A cut of capacity at most `22` whose two sides have counting mass at least
`1 / 40000` lies below the completeness threshold. -/
theorem completeness_ratio {N z T : ℝ} (hN : 0 < N)
    (hz : (1 : ℝ) / 40000 ≤ z) (hz' : (1 : ℝ) / 40000 ≤ 1 - z)
    (hT : T ≤ 22) : T / (N ^ 2 * (z * (1 - z))) < 10 ^ 12 / N ^ 2 := by
  have hz₀ : 0 < z := by linarith
  have hz₁ : 0 < 1 - z := by linarith
  have hvar : (1 / 40000 : ℝ) ^ 2 ≤ z * (1 - z) := by
    simpa only [pow_two] using
      mul_le_mul hz hz' (by norm_num : (0 : ℝ) ≤ 1 / 40000) hz₀.le
  have hgap : T < (10 : ℝ) ^ 12 * (z * (1 - z)) := by nlinarith
  have hvpos := mul_pos hz₀ hz₁
  have hdiv : T / (z * (1 - z)) < (10 : ℝ) ^ 12 := (div_lt_iff₀ hvpos).mpr hgap
  have hN₂ : 0 < N ^ 2 := sq_pos_of_pos hN
  calc
    _ = (T / (z * (1 - z))) / N ^ 2 := by rw [div_div, mul_comm]
    _ < _ := (div_lt_div_iff_of_pos_right hN₂).mpr hdiv

/-- Variance transfer and the tether bound contradict the comparison gap for a
nontrivial monochromatic-cluster cut. -/
theorem soundness_contradiction {κ z ν T L D : ℝ}
    (hκ : 0 < κ) (hz₀ : 0 < z) (hz₁ : z < 1) (hν : 0 ≤ ν) (hL : 0 ≤ L)
    (hsmall : T ≤ κ * (z * (1 - z)))
    (htether : 2 * κ * L ≤ T) (htransfer : z * (1 - z) ≤ 36 * ν + L)
    (hraw : D ≤ T) (hgap : 0 < ν → 100 * κ * ν < D) : False := by
  have ht : T ≤ κ * (36 * ν + L) :=
    hsmall.trans (mul_le_mul_of_nonneg_left htransfer hκ.le)
  have ht72 : T ≤ 72 * κ * ν := by nlinarith only [ht, htether]
  have hνpos : 0 < ν := by
    by_contra hn
    have hνzero : ν = 0 := le_antisymm (le_of_not_gt hn) hν
    rw [hνzero] at ht72 htransfer
    have hT : T ≤ 0 := by simpa using ht72
    have hLzero : L = 0 := by nlinarith [mul_pos hκ (show (0 : ℝ) < 2 by norm_num)]
    have hvarpos : 0 < z * (1 - z) := mul_pos hz₀ (sub_pos.mpr hz₁)
    nlinarith only [htransfer, hLzero, hvarpos]
  have hpositive := mul_pos hκ hνpos
  have hno := hgap hνpos
  nlinarith only [ht72, hraw, hno, hpositive]

end UniformSparsestCut

end OAI
