import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalSieveScale
import Mathlib.Analysis.PSeries

namespace OAI

/-! The explicit prime-band endpoints from MRT, Definition 2.1. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def mrtBandLower (P Q : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((j : ℝ) ^ (4 * j) * (Real.log Q) ^ (j - 1) * Real.log P)

noncomputable def mrtBandUpper (Q : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((j : ℝ) ^ (4 * j + 2) * (Real.log Q) ^ j)

lemma mrtBandLower_one (P Q : ℝ) (hP : 0 < P) : mrtBandLower P Q 1 = P := by
  simp [mrtBandLower, Real.exp_log hP]

lemma mrtBandUpper_one (Q : ℝ) (hQ : 0 < Q) : mrtBandUpper Q 1 = Q := by
  simp [mrtBandUpper, Real.exp_log hQ]

lemma mrt_band_log_ratio (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j) (hQ : 1 < Q) :
    Real.log (mrtBandLower P Q j) / Real.log (mrtBandUpper Q j) =
      (Real.log P / Real.log Q) / (j : ℝ) ^ 2 := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hq0 : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [mrtBandLower, mrtBandUpper, Real.log_exp]
  rw [pow_add, hpow]
  field_simp [hj0, hq0]

lemma mrt_band_endpoints (P Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlogQ : 1 ≤ Real.log Q) :
    2 ≤ mrtBandLower P Q j ∧ mrtBandLower P Q j ≤ mrtBandUpper Q j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp0 : 0 < P := by linarith
  have hq0 : 0 < Q := hp0.trans_le hPQ
  have hlp : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hlpq : Real.log P ≤ Real.log Q := Real.log_le_log hp0 hPQ
  have hc : 1 ≤ (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hj1) (one_le_pow₀ hlogQ)
  constructor
  · calc
      2 ≤ P := hP
      _ = Real.exp (Real.log P) := (Real.exp_log hp0).symm
      _ ≤ mrtBandLower P Q j := by
        apply Real.exp_le_exp.mpr
        nlinarith
  · apply Real.exp_le_exp.mpr
    have hpow : (Real.log Q) ^ j = (Real.log Q) ^ (j - 1) * Real.log Q := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log P ≤
          (j : ℝ) ^ (4 * j) * Real.log Q ^ (j - 1) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlpq (by positivity)
      _ = (j : ℝ) ^ (4 * j) * Real.log Q ^ j := by rw [hpow]; ring
      _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hj1 (by omega)) (by positivity)

lemma mrt_band_index_le_log_upper (Q : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hlogQ : 1 ≤ Real.log Q) : (j : ℝ) ≤ Real.log (mrtBandUpper Q j) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  simp only [mrtBandUpper, Real.log_exp]
  calc
    (j : ℝ) ≤ (j : ℝ) ^ (4 * j + 2) := by
      simpa using pow_le_pow_right₀ hj1 (show 1 ≤ 4 * j + 2 by omega)
    _ ≤ (j : ℝ) ^ (4 * j + 2) * Real.log Q ^ j := by
      have hh := one_le_pow₀ (n := j) hlogQ
      nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ j) (4 * j + 2)]

lemma mrt_band_ratio_sum (P Q : ℝ) (J : ℕ) (hP : 1 ≤ P) (hQ : 1 < Q) :
    (∑ j ∈ Icc 1 J, Real.log (mrtBandLower P Q j) /
      Real.log (mrtBandUpper Q j)) ≤ 2 * Real.log P / Real.log Q := by
  have hr : 0 ≤ Real.log P / Real.log Q := div_nonneg
    (Real.log_nonneg hP) (Real.log_pos hQ).le
  have hs : (∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹) ≤ 2 := by
    have he : Icc 1 J = Ioo 0 (J + 1) := by ext j; simp; omega
    rw [he]
    simpa using (sum_Ioo_inv_sq_le (α := ℝ) 0 (J + 1))
  calc
    _ = (Real.log P / Real.log Q) * ∑ j ∈ Icc 1 J, ((j : ℝ) ^ 2)⁻¹ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [mrt_band_log_ratio P Q j (mem_Icc.mp hj).1 hQ]
      ring
    _ ≤ (Real.log P / Real.log Q) * 2 := mul_le_mul_of_nonneg_left hs hr
    _ = _ := by ring

end TwoPointCorrelations

end OAI
