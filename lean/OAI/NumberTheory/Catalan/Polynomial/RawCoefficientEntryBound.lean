import OAI.NumberTheory.Catalan.Determinants.RawMinorCoefficientExpansion
import OAI.NumberTheory.Catalan.Estimates.UnconvolvedVectorBounds

namespace OAI


noncomputable section

namespace InternalCatalan

def discrepancyNormFactor (z : ℚ) : ℝ :=
  max 1 (max ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ ‖smoothingMoment 0 1‖)

theorem one_le_discrepancyNormFactor (z : ℚ) : 1 ≤ discrepancyNormFactor z :=
  le_max_left _ _

theorem discrepancyNormFactor_nonneg (z : ℚ) : 0 ≤ discrepancyNormFactor z :=
  zero_le_one.trans (one_le_discrepancyNormFactor z)

theorem rawCoefficientEntry_norm_le (z : ℚ) {N r j : ℕ}
    (hN : 0 < N) (hj : j < L N) (t : Fin 3) (u : rawCoefficientIndex N t) :
    ‖rawCoefficientVector N r j t u.val * rawCoefficientScalar z N j t u.val‖ ≤
      (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) *
        (2 : ℝ) ^ (-(if t = 0 then (Cdegree N : ℤ)
          else if t = 1 then 2 * (u.val : ℤ) + (j : ℤ) - (H N : ℤ)
          else (u.val : ℤ))) := by
  have hjH : j < H N := by unfold L H at *; omega
  have hHone : 1 ≤ (H N : ℝ) := by
    have hH : 1 ≤ H N := by unfold H; omega
    exact_mod_cast hH
  have hHsq : 1 ≤ (H N : ℝ) ^ 2 := by
    nlinarith only [hHone, sq_nonneg ((H N : ℝ) - 1)]
  have hFone := one_le_discrepancyNormFactor z
  have hFzero := discrepancyNormFactor_nonneg z
  have hFcommon : discrepancyNormFactor z ≤
      8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by
    nlinarith only [hFone, mul_le_mul_of_nonneg_left hHsq hFzero]
  have hScommon : 8 * (H N : ℝ) ^ 2 ≤
      8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hFone (sq_nonneg (H N : ℝ))]
  have he1 : ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ ≤ discrepancyNormFactor z :=
    (le_max_left _ _).trans (le_max_right _ _)
  have he2 : ‖smoothingMoment 0 1‖ ≤ discrepancyNormFactor z :=
    (le_max_right _ _).trans (le_max_right _ _)
  by_cases h0 : t = 0
  · simp only [rawCoefficientVector, rawCoefficientScalar, h0, ite_eq_left, mul_one]
    have hs := (smoothingColumn_norm_le N r j hjH).trans
      (div_le_div_of_nonneg_right hScommon (by positivity :
        (0 : ℝ) ≤ (2 : ℝ) ^ Cdegree N))
    simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using hs
  · have hu : u.val < Cdegree N := by
      simpa only [rawCoefficientIndex, ite_eq_right h0] using u.isLt
    by_cases h1 : t = 1
    · simp only [rawCoefficientVector, rawCoefficientScalar, h1, ite_true]
      rw [norm_mul]
      calc
        _ ≤ (2 : ℝ) ^ (1 - (u.val : ℤ)) *
            (‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ *
              (2 : ℝ) ^ ((H N : ℤ) - 1 - u.val - j)) :=
          mul_le_mul (unconvolvedP_entry_norm_le N r u.val)
            (exceptionScalar_norm_le z j hu) (norm_nonneg _) (by positivity)
        _ = ‖4 * (z : ℚ_[2]) - smoothingMoment 0 0‖ *
            (2 : ℝ) ^ (-(2 * (u.val : ℤ) + j - (H N : ℤ))) := by
          rw [mul_left_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have he : (1 - (u.val : ℤ)) + ((H N : ℤ) - 1 - u.val - j) =
              -(2 * (u.val : ℤ) + j - (H N : ℤ)) := by ring
          rw [he]
        _ ≤ _ := mul_le_mul_of_nonneg_right (he1.trans hFcommon) (by positivity)
    · have hp : (2 : ℝ) ^ Nat.log 2 (H N) ≤ (H N : ℝ) + 1 := by
        exact_mod_cast Nat.pow_log_le_add_one 2 (H N)
      have hp' : (2 : ℝ) ^ Nat.log 2 (H N) ≤ 2 * (H N : ℝ) := by
        linarith only [hp, hHone]
      have hlog : 2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N)) ≤ 8 * (H N : ℝ) ^ 2 := by
        have hp2 := mul_nonneg (sub_nonneg.mpr hp')
          (show 0 ≤ 2 * (H N : ℝ) + (2 : ℝ) ^ Nat.log 2 (H N) by positivity)
        rw [Nat.mul_comm 2 (Nat.log 2 (H N)), pow_mul]
        nlinarith only [hp2]
      have hBcommon : max ‖-smoothingMoment 0 1‖
          (2 * (2 : ℝ) ^ (2 * Nat.log 2 (H N))) ≤
          8 * discrepancyNormFactor z * (H N : ℝ) ^ 2 := by
        rw [norm_neg]
        exact max_le (he2.trans hFcommon) (hlog.trans hScommon)
      simp only [rawCoefficientVector, rawCoefficientScalar, h0, h1, ite_false]
      rw [norm_mul]
      calc
        _ ≤ (2 : ℝ) ^ (-(u.val : ℤ)) *
            (8 * discrepancyNormFactor z * (H N : ℝ) ^ 2) :=
          mul_le_mul (unconvolvedD_entry_norm_le N r u.val)
            ((boundaryScalar_norm_le hu hjH).trans hBcommon)
            (norm_nonneg _) (by positivity)
        _ = _ := mul_comm _ _

end InternalCatalan

end

end OAI
