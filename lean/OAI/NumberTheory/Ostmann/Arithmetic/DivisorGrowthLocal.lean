import Mathlib

namespace OAI

namespace Ostmann.Arithmetic
open scoped BigOperators

theorem exists_linear_le_geometric {b : ℝ} (hb : 1 < b) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ e : ℕ, (e : ℝ) + 1 ≤ C * b ^ e := by
  let C : ℝ := 1 + (b - 1)⁻¹
  have hb1 : 0 < b - 1 := by linarith
  have hC : 1 ≤ C := by
    dsimp [C]
    have h := inv_nonneg.mpr hb1.le
    linarith
  have hCb : C * (b - 1) = b := by dsimp [C]; field_simp; ring
  refine ⟨C, hC, fun e => ?_⟩
  have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ b by linarith) e
  have hscale := mul_le_mul_of_nonneg_left hbern (by linarith : 0 ≤ C)
  have he : (0 : ℝ) ≤ e := by positivity
  have he' : (e : ℝ) ≤ e * b := by nlinarith
  nlinarith [mul_assoc C (e : ℝ) (b - 1)]

theorem exponent_succ_le_two_pow (e : ℕ) : (e : ℝ) + 1 ≤ (2 : ℝ) ^ e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    rw [pow_succ]
    push_cast
    have : (0 : ℝ) ≤ e := by positivity
    nlinarith

theorem prime_local_divisor_bounds (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, Nat.Prime p → ∀ e : ℕ,
      (e : ℝ) + 1 ≤ (if p < P then C else 1) * ((p : ℝ) ^ ε) ^ e := by
  obtain ⟨C, hC, hCb⟩ := exists_linear_le_geometric
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hε)
  have ht : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ ε) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨P, hP⟩ := Filter.eventually_atTop.mp (ht.eventually_ge_atTop 2)
  refine ⟨P, C, hC, fun p hp e => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  by_cases hsmall : p < P
  · simp only [hsmall, ite_true]
    exact (hCb e).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_le_rpow (by norm_num) hp2 hε.le) e) (by linarith))
  · simp only [hsmall, ite_false, one_mul]
    exact (exponent_succ_le_two_pow e).trans
      (pow_le_pow_left₀ (by norm_num) (hP p (by omega)) e)

end Ostmann.Arithmetic

end OAI
