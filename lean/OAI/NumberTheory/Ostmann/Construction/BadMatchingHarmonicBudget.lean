import OAI.NumberTheory.Ostmann.Construction.SeparatedMatchingCount
import OAI.NumberTheory.Ostmann.Construction.FactorialExponential

namespace OAI

/-! # The bad matching count after its original harmonic normalization -/

namespace Ostmann
open scoped BigOperators Classical

theorem factorial_harmonic_entropy (r m : ℕ) (L z : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L) :
    (m.factorial : ℝ) ^ r * (L⁻¹) ^ (r * m) ≤
      Real.exp (Real.log z * (r * m : ℕ)) := by
  have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
  have hratio : (m : ℝ) * L⁻¹ ≤ z := by
    have hh := mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hL.le)
    simpa only [mul_assoc, mul_inv_cancel₀ hL.ne', mul_one] using hh
  calc
    _ ≤ ((m : ℝ) ^ m) ^ r * (L⁻¹) ^ (r * m) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hfac r) (by positivity)
    _ = ((m : ℝ) * L⁻¹) ^ (r * m) := by rw [← pow_mul, Nat.mul_comm m r, mul_pow]
    _ ≤ z ^ (r * m) := pow_le_pow_left₀ (by positivity) hratio _
    _ = _ := by
      rw [← Real.exp_log hz, ← Real.exp_nat_mul]
      congr 1
      simp only [Real.log_exp]
      ring

/-- This is the bad-part exponent before the transfer gap is subtracted.
The only prefactor left is constant at fixed tree depth and nonbulk slots. -/
theorem bad_separated_harmonic_bound {r m : ℕ} {N : Type*} [Fintype N]
    (hr : 1 ≤ r) (hm0 : 0 < m) (L z C : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L) :
    (Fintype.card {e : PartitionMatching (@sumSide (Fin r × Fin m) N)
      (@sumSide (Fin r × Fin m) N) // BadBulkArrangement (separatedMatchingLeft e)} : ℝ) *
      (L⁻¹) ^ (r * m) * Real.exp (C * (r * m : ℕ)) ≤
      (((r + 1) * r ^ (2 * r) : ℕ) : ℝ) * (Fintype.card N).factorial *
        Real.exp ((Real.log z + Real.log r / 4 + C + 1 / 4) * (r * m : ℕ)) := by
  have hc := bad_separated_matching_bound (N := N) hr hm0
  have hf := factorial_harmonic_entropy r m L z hL hz hm
  calc
    _ ≤ ((((r + 1) * r ^ (2 * r) : ℕ) : ℝ) * (m.factorial : ℝ) ^ r *
        Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4) * (Fintype.card N).factorial) *
        (L⁻¹) ^ (r * m) * Real.exp (C * (r * m : ℕ)) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
    _ = (((r + 1) * r ^ (2 * r) : ℕ) : ℝ) * (Fintype.card N).factorial *
        ((m.factorial : ℝ) ^ r * (L⁻¹) ^ (r * m)) *
        (Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4) * Real.exp (C * (r * m : ℕ))) := by ring
    _ ≤ (((r + 1) * r ^ (2 * r) : ℕ) : ℝ) * (Fintype.card N).factorial *
        Real.exp (Real.log z * (r * m : ℕ)) *
        (Real.exp ((m : ℝ) * r * (Real.log r + 1) / 4) * Real.exp (C * (r * m : ℕ))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by positivity)) (by positivity)
    _ = _ := by
      simp only [mul_assoc, ← Real.exp_add]
      congr 3
      push_cast
      ring

end Ostmann

end OAI
