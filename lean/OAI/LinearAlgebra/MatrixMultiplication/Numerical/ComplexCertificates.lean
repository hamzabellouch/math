import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexCertificatesLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

noncomputable section

namespace MatrixMultiplication.ComplexCertificates

def curveU : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 3)
def curveV : ℝ := (19 : ℝ) ^ ((2 : ℝ) / 3)
def curveZ : ℝ := 8 + 12 * curveU + 6 * curveU ^ 2 + curveV
def curveG : ℝ :=
  (12 * curveU * (1 + curveU) * Real.log 2 + curveV * Real.log 19) / curveZ
def curveH : ℝ := Real.log curveZ - (2 / 3 : ℝ) * curveG

theorem curveU_cube : curveU ^ 3 = 4 := by
  rw [curveU, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem curveV_cube : curveV ^ 3 = 361 := by
  rw [curveV, ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 19)]
  norm_num

theorem curveU_bounds :
    (158739 : ℝ) / 100000 < curveU ∧ curveU < (79371 : ℝ) / 50000 := by
  have h0 : 0 ≤ curveU := Real.rpow_nonneg (by norm_num) _
  constructor
  · apply (pow_lt_pow_iff_left₀ (by norm_num) h0 (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveU_cube]
    norm_num
  · apply (pow_lt_pow_iff_left₀ h0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveU_cube]
    norm_num

theorem curveV_bounds :
    (71203 : ℝ) / 10000 < curveV ∧ curveV < (14241 : ℝ) / 2000 := by
  have h0 : 0 ≤ curveV := Real.rpow_nonneg (by norm_num) _
  constructor
  · apply (pow_lt_pow_iff_left₀ (by norm_num) h0 (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveV_cube]
    norm_num
  · apply (pow_lt_pow_iff_left₀ h0 (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).1
    rw [curveV_cube]
    norm_num

theorem curveZ_bounds :
    (246439 : ℝ) / 5000 < curveZ ∧ curveZ < (49289 : ℝ) / 1000 := by
  obtain ⟨hu, hu'⟩ := curveU_bounds
  obtain ⟨hv, hv'⟩ := curveV_bounds
  have hu0 : 0 ≤ curveU := by linarith
  constructor
  · have h : 8 + 12 * ((158739 : ℝ) / 100000) +
        6 * ((158739 : ℝ) / 100000) ^ 2 + (71203 : ℝ) / 10000 ≤ curveZ := by
      dsimp [curveZ]
      gcongr
    norm_num at h ⊢
    linarith
  · have h : curveZ ≤ 8 + 12 * ((79371 : ℝ) / 50000) +
        6 * ((79371 : ℝ) / 50000) ^ 2 + (14241 : ℝ) / 2000 := by
      dsimp [curveZ]
      gcongr
    norm_num at h ⊢
    linarith

theorem curveG_bounds :
    (27961 : ℝ) / 25000 < curveG ∧ curveG < (6991 : ℝ) / 6250 := by
  obtain ⟨hu, hu'⟩ := curveU_bounds
  obtain ⟨hv, hv'⟩ := curveV_bounds
  obtain ⟨hz, hz'⟩ := curveZ_bounds
  obtain ⟨hl2, hh2⟩ := log_two_bounds
  obtain ⟨hl19, hh19⟩ := log_nineteen_bounds
  have hu0 : 0 ≤ curveU := by linarith
  have hv0 : 0 ≤ curveV := by linarith
  have hz0 : 0 < curveZ := by linarith
  have hl20 : 0 ≤ Real.log 2 := by linarith
  have hl190 : 0 ≤ Real.log 19 := by linarith
  have hnlo :
      12 * ((158739 : ℝ) / 100000) * (1 + (158739 : ℝ) / 100000) *
        ((34657 : ℝ) / 50000) + ((71203 : ℝ) / 10000) * ((7361 : ℝ) / 2500) ≤
      12 * curveU * (1 + curveU) * Real.log 2 + curveV * Real.log 19 := by
    gcongr
  have hnhi :
      12 * curveU * (1 + curveU) * Real.log 2 + curveV * Real.log 19 ≤
      12 * ((79371 : ℝ) / 50000) * (1 + (79371 : ℝ) / 50000) *
        ((17329 : ℝ) / 25000) + ((14241 : ℝ) / 2000) * ((5889 : ℝ) / 2000) := by
    gcongr
  constructor
  · apply (lt_div_iff₀ hz0).2
    norm_num at hnlo
    nlinarith
  · apply (div_lt_iff₀ hz0).2
    norm_num at hnhi
    nlinarith

theorem curveH_bounds :
    (31519 : ℝ) / 10000 < curveH ∧ curveH < (15761 : ℝ) / 5000 := by
  obtain ⟨hg, hg'⟩ := curveG_bounds
  obtain ⟨hz, hz'⟩ := curveZ_bounds
  have hz0 : 0 < curveZ := by linarith
  have hlo : (77953 : ℝ) / 20000 < Real.log curveZ :=
    log_curve_lower.trans (Real.log_lt_log (by norm_num) hz)
  have hhi : Real.log curveZ < (97443 : ℝ) / 25000 :=
    (Real.log_lt_log hz0 hz').trans log_curve_upper
  dsimp [curveH]
  constructor <;> linarith

def squareLeafCount : ℕ := 2995461856366867388223311649574852466276480577

theorem square_log_lower :
    (523471 : ℝ) / 5000 < Real.log (squareLeafCount : ℝ) := by
  have hc : (59 / 20 : ℝ) * 10 ^ 45 < (squareLeafCount : ℝ) := by
    norm_num [squareLeafCount]
  have hlo := Real.log_lt_log (by positivity : (0 : ℝ) < (59 / 20 : ℝ) * 10 ^ 45) hc
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow] at hlo
  have h1 := log_square_mantissa_lower
  have h2 := log_ten_lower
  norm_num at hlo
  linarith

end MatrixMultiplication.ComplexCertificates

end

end OAI
