import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Determinants.RealColumnDeterminant

namespace OAI

noncomputable section

open Set Polynomial

namespace InternalCatalan

def realRowAmplitude (N r : ℕ) (t : ℝ) : ℝ :=
  (realPoly (rowP N r)).eval t - (3 / 2 : ℝ) *
    (if 0 < t then Real.sqrt (1 - t ^ 2) / t * (realPoly (rowD N r)).eval t else 0)

theorem realRowAmplitude_of_nonpos (N r : ℕ) {t : ℝ} (ht : t ≤ 0) :
    realRowAmplitude N r t = (realPoly (rowP N r)).eval t := by
  simp [realRowAmplitude, not_lt.mpr ht]

theorem realRowAmplitude_of_neg (N r : ℕ) {t : ℝ} (ht : t < 0) :
    realRowAmplitude N r t = (realPoly (rowP N r)).eval t :=
  realRowAmplitude_of_nonpos N r ht.le

theorem realRowAmplitude_of_pos (N r : ℕ) {t : ℝ} (ht : 0 < t) :
    realRowAmplitude N r t = (realPoly (rowP N r)).eval t -
      (3 / 2 : ℝ) * (Real.sqrt (1 - t ^ 2) / t * (realPoly (rowD N r)).eval t) := by
  simp [realRowAmplitude, ht]

theorem realRowAmplitude_weighted_eq (N r : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (|t| / Real.sqrt (1 - t ^ 2)) * realRowAmplitude N r t =
      (|t| / Real.sqrt (1 - t ^ 2)) * (realPoly (rowP N r)).eval t -
        (3 / 2 : ℝ) * (if 0 < t then (realPoly (rowD N r)).eval t else 0) := by
  by_cases hp : 0 < t
  · rw [realRowAmplitude_of_pos N r hp, ite_eq_left hp]
    have ht0 : t ≠ 0 := hp.ne'
    have hrad : 0 < 1 - t ^ 2 := by
      have hprod := mul_pos (sub_pos.mpr ht.2) (show (0 : ℝ) < 1 + t by linarith [ht.1])
      nlinarith
    have hs0 : Real.sqrt (1 - t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr hrad).ne'
    have hcancel :
        (|t| / Real.sqrt (1 - t ^ 2)) * (Real.sqrt (1 - t ^ 2) / t) = 1 := by
      rw [abs_of_pos hp]
      field_simp [ht0, hs0]
    calc
      _ = (|t| / Real.sqrt (1 - t ^ 2)) * (realPoly (rowP N r)).eval t -
          (3 / 2 : ℝ) *
            (((|t| / Real.sqrt (1 - t ^ 2)) * (Real.sqrt (1 - t ^ 2) / t)) *
              (realPoly (rowD N r)).eval t) := by ring
      _ = _ := by rw [hcancel]; ring
  · rw [realRowAmplitude_of_nonpos N r (le_of_not_gt hp), ite_eq_right hp]
    simp

theorem realRowAmplitude_kernel_eq (N r : ℕ) (Q : ℝ[X]) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (s : ℝ) :
    (|t| / Real.sqrt (1 - t ^ 2)) * (realRowAmplitude N r t * Q.eval s) /
        (1 - t * s) =
      (|t| / Real.sqrt (1 - t ^ 2)) * ((realPoly (rowP N r)).eval t * Q.eval s) /
          (1 - t * s) -
        (3 / 2 : ℝ) *
          (if 0 < t then (realPoly (rowD N r)).eval t * Q.eval s / (1 - t * s)
            else 0) := by
  calc
    _ = ((|t| / Real.sqrt (1 - t ^ 2)) * realRowAmplitude N r t) * Q.eval s /
        (1 - t * s) := by ring
    _ = ((|t| / Real.sqrt (1 - t ^ 2)) * (realPoly (rowP N r)).eval t -
        (3 / 2 : ℝ) * (if 0 < t then (realPoly (rowD N r)).eval t else 0)) *
          Q.eval s / (1 - t * s) := by rw [realRowAmplitude_weighted_eq N r ht]
    _ = _ := by
      by_cases hp : 0 < t
      · simp only [ite_eq_left hp]
        ring
      · simp only [ite_eq_right hp]
        ring

end InternalCatalan

end

end OAI
