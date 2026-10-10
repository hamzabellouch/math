import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.NumberTheory.Ostmann.Construction.HarmonicTuplePointBound

namespace OAI

/-! # Cancelling the external pivot count against the H endpoint product -/

namespace Ostmann
open scoped BigOperators

theorem natInterval_card_le_upper (a b : ℕ) (ha : 0 < a) :
    (Finset.Icc a b).card ≤ b := by
  rw [Nat.card_Icc]
  omega

theorem diagonal_endpoint_cancellation {H : Type*} [Fintype H]
    (a b : ℕ) (ha : 0 < a) (lower : H → ℝ) (hlower : ∀ h, 0 < lower h)
    (gap : ℝ) (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, lower h) :
    ((Finset.Icc a b).card : ℝ) * (∏ h, lower h)⁻¹ ≤ Real.exp (-gap) := by
  have hprod : 0 < ∏ h, lower h := Finset.prod_pos (fun h _ => hlower h)
  have hc : ((Finset.Icc a b).card : ℝ) ≤ b := by exact_mod_cast natInterval_card_le_upper a b ha
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hprod]
  calc
    _ ≤ (b : ℝ) := hc
    _ ≤ (Real.exp gap)⁻¹ * ∏ h, lower h := by
      have hh := mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr (Real.exp_pos gap).le)
      simpa only [← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero gap), one_mul] using hh

theorem finite_pivot_sum_bound (a b : ℕ) (ha : 0 < a)
    (F : ℕ → ℂ) (A B gap : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (lower : Type*) [Fintype lower] (lo : lower → ℝ) (hlo : ∀ h, 0 < lo h)
    (hgap : Real.exp gap * (b : ℝ) ≤ ∏ h, lo h)
    (hF : ∀ M ∈ Finset.Icc a b, ‖F M‖ ≤ A * (∏ h, lo h)⁻¹ * B) :
    (∑ M ∈ Finset.Icc a b, (F M).re) ≤ Real.exp (-gap) * A * B := by
  calc
    _ ≤ ∑ M ∈ Finset.Icc a b, ‖F M‖ :=
      Finset.sum_le_sum (fun M _ => Complex.re_le_norm (F M))
    _ ≤ ∑ _M ∈ Finset.Icc a b, A * (∏ h, lo h)⁻¹ * B :=
      Finset.sum_le_sum (fun M hM => hF M hM)
    _ = (((Finset.Icc a b).card : ℝ) * (∏ h, lo h)⁻¹) * A * B := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (diagonal_endpoint_cancellation a b ha lo hlo gap hgap) hA) hB

end Ostmann

end OAI
