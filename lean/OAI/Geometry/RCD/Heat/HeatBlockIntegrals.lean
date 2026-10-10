import OAI.Geometry.RCD.Heat.GaussianTimeConvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # Integrating the uniform bounds on source time blocks -/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- A scaled pointwise block bound gives the same integral budget on
any time interval of length at most the square of that scale. -/
theorem scaled_block_integral_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b s B : ℝ}
    (hs : 0 < s) (hab : a ≤ b) (hlength : b - a ≤ s ^ 2) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Ioc a b, s ^ 2 * ‖f t‖ ≤ B) :
    ‖∫ t in a..b, f t‖ ≤ B := by
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hh : ∀ t ∈ uIoc a b, ‖f t‖ ≤ B / s ^ 2 := by
    intro t ht
    have ht' : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using ht
    exact (le_div_iff₀ hs2).mpr (by simpa only [mul_comm] using hbound t ht')
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hh
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hi
  calc
    _ ≤ (B / s ^ 2) * (b - a) := hi
    _ ≤ (B / s ^ 2) * s ^ 2 := mul_le_mul_of_nonneg_left hlength (div_nonneg hB hs2.le)
    _ = B := div_mul_cancel₀ _ hs2.ne'

/-- The full short-time interval consumes exactly one source-envelope
budget, once the uniform scaled estimate is available. -/
theorem short_time_integral_norm_le {f : ℝ → ℝ} {s B : ℝ}
    (hs : 0 < s) (hB : 0 ≤ B)
    (hbound : ∀ t, 0 < t → t ≤ s ^ 2 → s ^ 2 * |f t| ≤ B) :
    |∫ t in (0 : ℝ)..s ^ 2, f t| ≤ B := by
  have hh := scaled_block_integral_norm_le (f := f) (a := 0) (b := s ^ 2) hs (sq_nonneg s)
    (by simp only [sub_zero]; exact le_rfl) hB
    (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ht.1 ht.2)
  simpa only [Real.norm_eq_abs] using hh

/-- The quarter-square to square interval is the actual long-time block. -/
theorem dyadic_time_integral_norm_le {f : ℝ → ℝ} {s B : ℝ}
    (hs : 0 < s) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc (s ^ 2 / 4) (s ^ 2), s ^ 2 * |f t| ≤ B) :
    |∫ t in (s ^ 2 / 4)..s ^ 2, f t| ≤ B := by
  have hh := scaled_block_integral_norm_le (f := f) (a := s ^ 2 / 4) (b := s ^ 2) hs
    (by nlinarith [sq_nonneg s]) (by nlinarith [sq_nonneg s]) hB
    (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ⟨ht.1.le, ht.2⟩)
  simpa only [Real.norm_eq_abs] using hh

end RegularPointCoordinates

end

end OAI
