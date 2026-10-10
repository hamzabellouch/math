import OAI.NumberTheory.TwoPoint.Fourier.MinorArcBilinearSieve
import Mathlib.Data.Nat.Cast.Order.Field

namespace OAI

/-! The finite cofactor cutoff needed by the literal short-window sum. -/

namespace TwoPointCorrelations

open Finset

lemma minor_arc_cofactor_cutoff (X H R p k : ℕ) (hR : 0 < R)
    (hRp : R ≤ p) (hk : k < X) :
    (k + H) / p < (X + H) / R + 1 := by
  have h₁ : (k + H) / p ≤ (k + H) / R := Nat.div_le_div_left hRp hR
  have h₂ : (k + H) / R ≤ (X + H) / R := Nat.div_le_div_right (by omega)
  omega

lemma minor_arc_cofactor_cutoff_bound (X H R : ℕ) (hR : 0 < R)
    (hRX : R ≤ X) (hHX : H ≤ X) :
    (((X + H) / R + 1 : ℕ) : ℝ) ≤ 3 * (X : ℝ) / R := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hHX' : (H : ℝ) ≤ X := by exact_mod_cast hHX
  have hRX' : (R : ℝ) ≤ X := by exact_mod_cast hRX
  have hdiv : (((X + H) / R : ℕ) : ℝ) ≤ ((X : ℝ) + H) / R := by
    simpa only [Nat.cast_add] using (Nat.cast_div_le (m := X + H) (n := R) (α := ℝ))
  push_cast
  calc
    _ ≤ ((X : ℝ) + H) / R + 1 := add_le_add hdiv le_rfl
    _ ≤ 3 * (X : ℝ) / R := by
      apply (le_div_iff₀ hR0).mpr
      rw [add_mul, div_mul_cancel₀ _ hR0.ne', one_mul]
      linarith

lemma minor_arc_origin_factor_bound (X H : ℕ) (hH : 1 ≤ H) :
    (X * (3 * H + 1) ^ 3 : ℕ) ≤ 64 * (X : ℝ) * (H : ℝ) ^ 3 := by
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hbase : 3 * (H : ℝ) + 1 ≤ 4 * H := by linarith
  have hc := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * (H : ℝ) + 1) hbase 3
  push_cast
  calc
    _ ≤ (X : ℝ) * (4 * H) ^ 3 := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg X)
    _ = _ := by ring

lemma minor_arc_cofactor_total_bound (X H R : ℕ) (hR : 0 < R)
    (hRX : R ≤ X) (hHX : H ≤ X) (hH : 1 ≤ H) :
    ((((X + H) / R + 1 : ℕ) : ℝ) ^ 3 *
        (X * (3 * H + 1) ^ 3 : ℕ) * H * (R : ℝ) ^ 3) ≤
      1728 * (X : ℝ) ^ 4 * (H : ℝ) ^ 4 := by
  have hR0 : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hM := minor_arc_cofactor_cutoff_bound X H R hR hRX hHX
  have hO := minor_arc_origin_factor_bound X H hH
  calc
    ((((X + H) / R + 1 : ℕ) : ℝ) ^ 3 *
        (X * (3 * H + 1) ^ 3 : ℕ) * H * (R : ℝ) ^ 3) ≤
        (3 * (X : ℝ) / R) ^ 3 * (64 * (X : ℝ) * (H : ℝ) ^ 3) * H * (R : ℝ) ^ 3 := by
      gcongr
    _ = _ := by field_simp [hR0]; ring

end TwoPointCorrelations

end OAI
