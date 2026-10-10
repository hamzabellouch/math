import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexCharacterHadamard
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualRealZeroIndices

namespace OAI

/-! # Uniform control of differences of zero resolvents -/

namespace Ostmann

open Complex

private theorem ratio_triangle_bound (U V D A δ : ℝ)
    (hU : 0 < U) (hV : 0 < V) (_hD : 0 ≤ D) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hsep : δ ≤ U) (hDA : D ≤ A) (htri : V ≤ U + D) :
    D / (U * V) ≤ A * (1 + A / δ) / V ^ 2 := by
  have hratio : V / U ≤ 1 + A / δ := by
    calc
      V / U ≤ (U + D) / U := div_le_div_of_nonneg_right htri hU.le
      _ = 1 + D / U := by rw [add_div, div_self hU.ne']
      _ ≤ 1 + A / U := by gcongr
      _ ≤ 1 + A / δ := by gcongr
  calc
    D / (U * V) = (D * (V / U)) / V ^ 2 := by field_simp
    _ ≤ (A * (1 + A / δ)) / V ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul hDA hratio (div_nonneg hV.le hU.le) hA

/-- An inverse difference is controlled by the positive real zero kernel at
its reference point. This makes the bound summable over actual zeros. -/
theorem zero_resolvent_difference_bound (s w ρ : ℂ) (A δ : ℝ)
    (hA : 0 ≤ A) (hδ : 0 < δ) (hsep : δ ≤ ‖s - ρ‖)
    (hshift : ‖w - s‖ ≤ A) (hre : 1 ≤ (w - ρ).re) :
    ‖(s - ρ)⁻¹ - (w - ρ)⁻¹‖ ≤
      A * (1 + A / δ) * ((w - ρ)⁻¹).re := by
  have hsp : 0 < ‖s - ρ‖ := hδ.trans_le hsep
  have hwp : 0 < ‖w - ρ‖ := by
    have hh := (Complex.re_le_norm (w - ρ))
    linarith
  have hsn : s - ρ ≠ 0 := norm_pos_iff.mp hsp
  have hwn : w - ρ ≠ 0 := norm_pos_iff.mp hwp
  have htri : ‖w - ρ‖ ≤ ‖s - ρ‖ + ‖w - s‖ := by
    have hh := norm_add_le (s - ρ) (w - s)
    rw [show s - ρ + (w - s) = w - ρ by ring] at hh
    exact hh
  have hkernel : 1 / ‖w - ρ‖ ^ 2 ≤ ((w - ρ)⁻¹).re := by
    rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
    exact div_le_div_of_nonneg_right hre (sq_nonneg _)
  calc
    _ = ‖w - s‖ / (‖s - ρ‖ * ‖w - ρ‖) := by
      rw [inv_sub_inv hsn hwn, norm_div, norm_mul]
      congr 2
      ring
    _ ≤ A * (1 + A / δ) / ‖w - ρ‖ ^ 2 :=
      ratio_triangle_bound _ _ _ _ _ hsp hwp (norm_nonneg _) hA hδ hsep hshift htri
    _ = (A * (1 + A / δ)) * (1 / ‖w - ρ‖ ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hkernel (by positivity)

end Ostmann

end OAI
