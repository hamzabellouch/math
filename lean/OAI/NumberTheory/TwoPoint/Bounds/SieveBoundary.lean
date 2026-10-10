import OAI.NumberTheory.TwoPoint.Bounds.SieveModel
import Mathlib.Data.Nat.Choose.Bounds

namespace OAI

/-! Explicit accumulation of the finitely many CRT counting errors. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma elementarySymmetric_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y : ℝ) (hY : 0 ≤ Y) (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (j : ℕ) :
    elementarySymmetric P a j ≤ ((P.card : ℝ) * Y) ^ j := by
  calc
    _ ≤ ∑ _S ∈ P.powersetCard j, Y ^ j := by
      apply sum_le_sum
      intro S hS
      obtain ⟨hSP, hcard⟩ := mem_powersetCard.mp hS
      have hh : (∏ i ∈ S, a i) ≤ ∏ _i ∈ S, Y := by
        exact prod_le_prod₀ (fun i hi => (ha i (hSP hi)).1)
          (fun i hi => (ha i (hSP hi)).2)
      simpa only [prod_const, hcard] using hh
    _ = (P.card.choose j : ℝ) * Y ^ j := by
      simp only [sum_const, card_powersetCard, nsmul_eq_mul]
    _ ≤ (P.card : ℝ) ^ j * Y ^ j := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hY j)
      exact_mod_cast Nat.choose_le_pow P.card j
    _ = _ := (mul_pow _ _ _).symm

lemma truncatedElementary_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y : ℝ) (hY : 0 ≤ Y) (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (R : ℕ) :
    (∑ j ∈ range (R + 1), elementarySymmetric P a j) ≤
      (R + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ R := by
  have hb : 1 ≤ (P.card : ℝ) * Y + 1 := by
    linarith [show 0 ≤ (P.card : ℝ) * Y by positivity]
  calc
    _ ≤ ∑ _j ∈ range (R + 1), ((P.card : ℝ) * Y + 1) ^ R := by
      apply sum_le_sum
      intro j hj
      calc
        _ ≤ ((P.card : ℝ) * Y) ^ j := elementarySymmetric_crude P a Y hY ha j
        _ ≤ ((P.card : ℝ) * Y + 1) ^ j := by gcongr; linarith
        _ ≤ ((P.card : ℝ) * Y + 1) ^ R :=
          pow_le_pow_right₀ hb (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]

lemma sieveIntersectionError_factor {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (C : ℝ) (N R : ℕ) :
    sieveIntersectionError P (fun S => C / N * ∏ i ∈ S, a i) R =
      C / N * ∑ j ∈ range (R + 1), elementarySymmetric P a j := by
  simp only [sieveIntersectionError, elementarySymmetric, mul_sum]

/-- If an intersection indexed by `S` has normalized CRT error at most
`C * (∏ i∈S, a i) / N`, the whole finite truncation costs this explicit
quantity. In the application `a i` is the selected prime and `C=1` or `3`. -/
theorem sieveIntersectionError_crude {ι : Type*} (P : Finset ι) (a : ι → ℝ)
    (Y C : ℝ) (hY : 0 ≤ Y) (hC : 0 ≤ C)
    (ha : ∀ i ∈ P, 0 ≤ a i ∧ a i ≤ Y) (N R : ℕ) :
    sieveIntersectionError P (fun S => C / N * ∏ i ∈ S, a i) R ≤
      C / N * (R + 1 : ℕ) * ((P.card : ℝ) * Y + 1) ^ R := by
  rw [sieveIntersectionError_factor]
  exact (mul_le_mul_of_nonneg_left (truncatedElementary_crude P a Y hY ha R)
    (div_nonneg hC (Nat.cast_nonneg N))).trans_eq (by ring)

end TwoPointCorrelations

end OAI
