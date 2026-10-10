import OAI.NumberTheory.Ostmann.Characters.SparseMellinCoefficients

namespace OAI

/-! # The smaller principal coefficients of the sparse kernel -/
namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

theorem sparse_mellin_principal {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (t : ℝ) :
    mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x) 1 =
      (((p : ℝ) - 1)⁻¹ * (-t * E.card / p) : ℝ) := by
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) = (p : ℂ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  simp only [mellinCoefficient, MulChar.one_apply_coe, map_one, mul_one]
  rw [sum_units_eq_sum_nonzero, sparseAdditiveKernel_sum_nonzero E hE, hc]
  push_cast
  ring

theorem sparse_square_mellin_principal {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hsym : ∀ b, -b ∈ E ↔ b ∈ E) (t : ℝ) :
    mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ 2) 1 =
      (((p : ℝ) - 1)⁻¹ * (t ^ 2 * ((E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2)) : ℝ) := by
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) = (p : ℂ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  simp only [mellinCoefficient, MulChar.one_apply_coe, map_one, mul_one]
  rw [sum_units_eq_sum_nonzero (fun x : ZMod p => sparseAdditiveKernel E t x ^ 2)]
  simp_rw [pow_two]
  rw [sparseAdditiveKernel_square_sum_nonzero E hsym, hc]
  push_cast
  ring

theorem sparse_principal_coefficients_le {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) (hj : j = 1 ∨ j = 2) :
    ‖mellinCoefficient (fun x : (ZMod p)ˣ => sparseAdditiveKernel E t x ^ j) 1‖ ≤
      2 / p := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : 0 < (p : ℝ) - 1 := by linarith
  have hc : (E.card : ℝ) ≤ p := by
    have hh := Finset.card_le_card (Finset.subset_univ E)
    have hh' : E.card ≤ p := by simpa only [Finset.card_univ, ZMod.card] using hh
    exact_mod_cast hh'
  have he0 : 0 ≤ (E.card : ℝ) / p := by positivity
  have he1 : (E.card : ℝ) / p ≤ 1 := (div_le_one hp0).mpr hc
  have hi : ((p : ℝ) - 1)⁻¹ ≤ 2 / p := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hp1 hp0).mpr
    linarith
  apply le_trans _ hi
  rcases hj with rfl | rfl
  · simp only [pow_one, sparse_mellin_principal E hE t, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hp1), abs_div, abs_neg,
      abs_of_nonneg ht, abs_of_nonneg (show (0 : ℝ) ≤ E.card from Nat.cast_nonneg _), abs_of_pos hp0]
    have hh : t * E.card / p ≤ 1 := by
      calc
        _ = t * ((E.card : ℝ) / p) := by ring
        _ ≤ 1 * 1 := mul_le_mul ht1 he1 he0 (by norm_num)
        _ = 1 := by ring
    exact mul_le_of_le_one_right (inv_nonneg.mpr hp1.le) hh
  · rw [sparse_square_mellin_principal E hsym t, Complex.norm_real, Real.norm_eq_abs]
    have hn : 0 ≤ (E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2 := by nlinarith
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hp1.le) (mul_nonneg (sq_nonneg _) hn))]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    have hh : t ^ 2 * ((E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2) ≤ 1 := by
      nlinarith [mul_le_mul ht2 (show (E.card : ℝ) / p - ((E.card : ℝ) / p) ^ 2 ≤ 1 by nlinarith)
        hn (by norm_num : (0 : ℝ) ≤ 1)]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hp1.le) hh

end Ostmann

end OAI
