import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticSumBound

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem quadraticCorrelation_normalization {d e s v R : ℝ}
    (hd : 0 < d) (he : 0 < e) (hs : 0 < s) (hv : 0 < v) (hR : 0 < R) :
    (Real.sqrt (R / (s * v / d)))⁻¹ *
      (Real.sqrt (R / (s * v / e)))⁻¹ / s =
        v / (R * (Real.sqrt d * Real.sqrt e)) := by
  rw [Real.sqrt_div hR.le, Real.sqrt_div hR.le,
    Real.sqrt_div (mul_pos hs hv).le, Real.sqrt_div (mul_pos hs hv).le]
  have hd' := Real.sqrt_pos.mpr hd
  have he' := Real.sqrt_pos.mpr he
  have hR' := Real.sqrt_pos.mpr hR
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hR.le, Real.sq_sqrt (mul_pos hs hv).le]

theorem quadraticCorrelation_scale_cancellation {d e S v R : ℝ}
    (hd : 0 < d) (he : 0 < e) (hS : 0 < S) (hv : 0 < v) (hR : 0 < R) :
    (v / (R * (Real.sqrt d * Real.sqrt e))) *
      (Real.sqrt (R / (S * v / d)) * Real.sqrt (R / (S * v / e))) * S = 1 := by
  rw [Real.sqrt_div hR.le, Real.sqrt_div hR.le,
    Real.sqrt_div (mul_pos hS hv).le, Real.sqrt_div (mul_pos hS hv).le]
  have hd' := Real.sqrt_pos.mpr hd
  have he' := Real.sqrt_pos.mpr he
  have hR' := Real.sqrt_pos.mpr hR
  have hsv' := Real.sqrt_pos.mpr (mul_pos hS hv)
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hR.le, Real.sq_sqrt (mul_pos hv hS).le]
  ring

theorem quadraticCorrelation_scale_antitone {d S s v R : ℝ}
    (hd : 0 < d) (hS : 0 < S) (hSs : S ≤ s) (hv : 0 < v) (hR : 0 < R) :
    Real.sqrt (R / (s * v / d)) ≤ Real.sqrt (R / (S * v / d)) := by
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_left hR.le (div_pos (mul_pos hS hv) hd)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hSs hv.le) hd.le

theorem quadraticCorrelation_frequency_count {d e S v R : ℝ}
    (hd : 0 < d) (he : 0 < e) (hS : 0 < S) (hv : 0 < v) (hR : 0 < R) :
    (v / (R * (Real.sqrt d * Real.sqrt e))) *
      ((⌊Real.sqrt (R / (S * v / d))⌋₊ : ℝ) *
       (⌊Real.sqrt (R / (S * v / e))⌋₊ : ℝ)) * S ≤ 1 := by
  calc
    _ ≤ (v / (R * (Real.sqrt d * Real.sqrt e))) *
        (Real.sqrt (R / (S * v / d)) * Real.sqrt (R / (S * v / e))) * S := by
      apply mul_le_mul_of_nonneg_right _ hS.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (Nat.floor_le (Real.sqrt_nonneg _))
        (Nat.floor_le (Real.sqrt_nonneg _)) (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    _ = 1 := quadraticCorrelation_scale_cancellation hd he hS hv hR

end Ostmann.QuadraticCenter

end

end OAI
