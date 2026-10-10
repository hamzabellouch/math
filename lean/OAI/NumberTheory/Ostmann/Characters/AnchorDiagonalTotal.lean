import OAI.NumberTheory.Ostmann.Characters.AnchorMatchingCount
import OAI.NumberTheory.Ostmann.Construction.MatchedDiagonalEnergy

namespace OAI

/-! # Summing the code-preserving diagonal after counterpart normalization -/

namespace Ostmann

open scoped BigOperators Classical

abbrev AnchorMatchings {n : ℕ} (α : Fin n → ℤ) (m : ℕ) :=
  PartitionMatching
    (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode α x.1)
    (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode α x.1)

/-- The external pivot count is canceled before counting code-preserving
matchings. No unnormalized error is multiplied by the pivot population. -/
theorem anchor_preserving_diagonal_total {n m : ℕ} {P : Type*} [Fintype P]
    (α : Fin n → ℤ) (hα : ∀ j, α j = 1 ∨ α j = -1)
    (F : AnchorMatchings α m → P → ℂ) (C E T Δ κ : ℝ)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hP : (Fintype.card P : ℝ) ≤ Real.exp (T + κ))
    (hF : ∀ e p, ‖F e p‖ ≤ C * Real.exp (-(T + Δ)) * E) :
    ‖∑ e, ∑ p, F e p‖ ≤ ((2 * m : ℕ) : ℝ) ^ (2 ^ n * m) * C * Real.exp (κ - Δ) * E := by
  have he (e : AnchorMatchings α m) : ‖∑ p, F e p‖ ≤ C * Real.exp (κ - Δ) * E :=
    external_pivot_normalization (F e) C E T Δ κ hC hE hP (hF e)
  calc
    _ ≤ ∑ e, ‖∑ p, F e p‖ := norm_sum_le _ _
    _ ≤ ∑ _e : AnchorMatchings α m, C * Real.exp (κ - Δ) * E := Finset.sum_le_sum fun e _ => he e
    _ = (Fintype.card (AnchorMatchings α m) : ℝ) * (C * Real.exp (κ - Δ) * E) := by simp
    _ ≤ (((2 * m : ℕ) : ℝ) ^ (2 ^ n * m)) * (C * Real.exp (κ - Δ) * E) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_anchor_matching_le (m := m) α hα
    _ = _ := by ring

/-- The original harmonic normalizer provides exactly the `L^(-rm)`
needed to turn matching multiplicity into `z^(rm)`, with `m/L ≤ z`. -/
theorem matching_harmonic_entropy (N m : ℕ) (L z C : ℝ)
    (hL : 0 < L) (hz : 0 < z) (hm : (m : ℝ) ≤ z * L) :
    ((2 * m : ℕ) : ℝ) ^ N * (L⁻¹ ^ N * Real.exp (C * N)) ≤
      Real.exp ((Real.log z + (Real.log 2 + C)) * N) := by
  have hratio : (2 * m : ℕ) * L⁻¹ ≤ 2 * z := by
    have ht := mul_le_mul_of_nonneg_right hm (inv_nonneg.mpr hL.le)
    have hcancel : L * L⁻¹ = 1 := mul_inv_cancel₀ hL.ne'
    push_cast
    nlinarith [ht, hcancel]
  calc
    _ = (((2 * m : ℕ) : ℝ) * L⁻¹) ^ N * Real.exp (C * N) := by rw [mul_pow]; ring
    _ ≤ (2 * z) ^ N * Real.exp (C * N) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact pow_le_pow_left₀ (by positivity) hratio N
    _ = Real.exp ((Real.log z + (Real.log 2 + C)) * N) := by
      rw [← Real.exp_log (mul_pos (by norm_num) hz), ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [Real.log_mul (by norm_num) hz.ne']
      ring

end Ostmann

end OAI
