import Mathlib.Analysis.PSeries
import Mathlib.Tactic

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped BigOperators

theorem finite_nat_inv_sq_tail_le (s : Finset ℕ) {Y : ℝ} (hY : 0 < Y)
    (hs : ∀ n ∈ s, Y < (n : ℝ)) :
    (∑ n ∈ s, ((n : ℝ) ^ 2)⁻¹) ≤ 2 / Y := by
  have hsub : s ⊆ Finset.Ioo ⌊Y⌋₊ (s.sup id + 1) := by
    intro n hn
    exact Finset.mem_Ioo.mpr ⟨(Nat.floor_lt hY.le).mpr (hs n hn),
      Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  calc
    (∑ n ∈ s, ((n : ℝ) ^ 2)⁻¹) ≤
        ∑ n ∈ Finset.Ioo ⌊Y⌋₊ (s.sup id + 1), ((n : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 2 / ((⌊Y⌋₊ : ℝ) + 1) := sum_Ioo_inv_sq_le _ _
    _ ≤ 2 / Y := div_le_div_of_nonneg_left (by norm_num) hY (Nat.lt_floor_add_one Y).le

theorem finite_nat_card_le_real (s : Finset ℕ) {Y : ℝ} (hY : 0 ≤ Y)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ Y) : (s.card : ℝ) ≤ Y := by
  have hsub : s ⊆ Finset.Icc 1 ⌊Y⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(hs n hn).1, (Nat.le_floor_iff hY).mpr (hs n hn).2⟩
  have hc : s.card ≤ ⌊Y⌋₊ := by simpa using Finset.card_le_card hsub
  exact (show (s.card : ℝ) ≤ ⌊Y⌋₊ by exact_mod_cast hc).trans (Nat.floor_le hY)

theorem finite_nat_scaled_pow_sum_le (s : Finset ℕ) {X Y : ℝ} (hX : 0 < X) (hY : 0 ≤ Y)
    (hs : ∀ n ∈ s, 0 < n ∧ (n : ℝ) ≤ Y) (A : ℕ) :
    (∑ n ∈ s, ((n : ℝ) / X) ^ A) ≤ Y * (Y / X) ^ A := by
  calc
    _ ≤ ∑ _n ∈ s, (Y / X) ^ A := by
      apply Finset.sum_le_sum
      intro n hn
      gcongr
      exact (hs n hn).2
    _ = (s.card : ℝ) * (Y / X) ^ A := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (finite_nat_card_le_real s hY hs) (by positivity)

theorem finite_nat_scaled_inverse_pow_tail_le (s : Finset ℕ) {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hs : ∀ n ∈ s, Y < (n : ℝ)) (A : ℕ) :
    (∑ n ∈ s, (X / (n : ℝ)) ^ (A + 2)) ≤
      2 * X * (X / Y) ^ (A + 1) := by
  have hp (n : ℕ) (hn : n ∈ s) : 0 < (n : ℝ) := hY.trans (hs n hn)
  have hterm (n : ℕ) (hn : n ∈ s) :
      (X / (n : ℝ)) ^ (A + 2) ≤ X ^ (A + 2) * (Y ^ A)⁻¹ * ((n : ℝ) ^ 2)⁻¹ := by
    have hi : ((n : ℝ) ^ A)⁻¹ ≤ (Y ^ A)⁻¹ := by
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hY.le (hs n hn).le A)
    calc
      _ = X ^ (A + 2) * ((n : ℝ) ^ A)⁻¹ * ((n : ℝ) ^ 2)⁻¹ := by
        simp only [pow_add, div_eq_mul_inv]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hi (by positivity)) (by positivity)
  calc
    _ ≤ ∑ n ∈ s, X ^ (A + 2) * (Y ^ A)⁻¹ * ((n : ℝ) ^ 2)⁻¹ :=
      Finset.sum_le_sum hterm
    _ = X ^ (A + 2) * (Y ^ A)⁻¹ * (∑ n ∈ s, ((n : ℝ) ^ 2)⁻¹) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ X ^ (A + 2) * (Y ^ A)⁻¹ * (2 / Y) :=
      mul_le_mul_of_nonneg_left (finite_nat_inv_sq_tail_le s hY hs) (by positivity)
    _ = _ := by
      rw [div_pow, pow_succ, pow_add]
      field_simp
      ring

end Ostmann.QuadraticSieve

end OAI
