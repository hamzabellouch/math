import OAI.NumberTheory.Ostmann.Construction.TailPairDeletion
import OAI.NumberTheory.Ostmann.Characters.SparseWeightGrowth

namespace OAI

/-! # Numerical cost of the removed small endpoints -/
namespace Ostmann
open Filter
open scoped Classical BigOperators

 theorem sqrt_log_prefix_bound (C T : ℝ) (hC : 0 ≤ C) (hT : 1 ≤ T)
    (lo : ℕ) (hlo : 1 ≤ lo) (hupper : (lo : ℝ) ≤ Real.exp (9 * T / 10)) :
    C * Real.sqrt (lo : ℝ) * Real.log (lo : ℝ) ^ 2 ≤ C * Real.exp (9 * T / 20) * T ^ 2 := by
  have hlo1 : (1 : ℝ) ≤ lo := by exact_mod_cast hlo
  have hlop : (0 : ℝ) < lo := by linarith
  have hlog0 := Real.log_nonneg hlo1
  have hlog : Real.log (lo : ℝ) ≤ T := by
    have hh := Real.log_le_log hlop hupper
    rw [Real.log_exp] at hh
    linarith
  have hsqrt : Real.sqrt (lo : ℝ) ≤ Real.exp (9 * T / 20) := by
    have hh := Real.sqrt_le_sqrt hupper
    have he : Real.exp (9 * T / 10) = Real.exp (9 * T / 20) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rwa [he, Real.sqrt_sq (Real.exp_nonneg _)] at hh
  exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt hC)
    (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _) (by positivity)

 theorem endpoint_count_product_bound (C T a b u v : ℝ) (hC : 0 ≤ C)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (_hu : 0 ≤ u) (hv : 0 ≤ v)
    (haU : a ≤ C * Real.exp (9 * T / 20) * T ^ 2)
    (hbU : b ≤ C * Real.exp (9 * T / 20) * T ^ 2)
    (huU : u ≤ C * Real.exp (T / 2) * T ^ 2)
    (hvU : v ≤ C * Real.exp (T / 2) * T ^ 2) :
    a * v + u * b ≤ 2 * C ^ 2 * Real.exp (19 * T / 20) * T ^ 4 := by
  have h₁ := mul_le_mul haU hvU hv (by positivity)
  have h₂ := mul_le_mul huU hbU hb (by positivity)
  calc
    _ ≤ (C * Real.exp (9 * T / 20) * T ^ 2) * (C * Real.exp (T / 2) * T ^ 2) +
        (C * Real.exp (T / 2) * T ^ 2) * (C * Real.exp (9 * T / 20) * T ^ 2) :=
      add_le_add h₁ h₂
    _ = 2 * C ^ 2 * (Real.exp (9 * T / 20) * Real.exp (T / 2)) * T ^ 4 := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 3
      ring

 theorem eventual_small_endpoint_error (C D : ℝ) :
    ∀ᶠ L : ℝ in atTop,
      2 * C ^ 2 * Real.exp ((24 / 25 : ℝ) * Real.exp L) * Real.exp (5 * L) ≤
        Real.exp (Real.exp L) * Real.exp (-D * L) := by
  have hs := ((isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 by norm_num)).const_mul_left
    (25 * |D + 6|)).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hs, Real.tendsto_exp_atTop.eventually_ge_atTop (2 * C ^ 2),
    eventually_ge_atTop (0 : ℝ)] with L hsmall hC hL
  have hl : 25 * |D + 6| * L ≤ Real.exp L := by
    simpa only [pow_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 25 * |D + 6| * L), abs_of_pos (Real.exp_pos _)] using hsmall
  calc
    _ ≤ Real.exp L * Real.exp ((24 / 25 : ℝ) * Real.exp L) * Real.exp (5 * L) := by
      gcongr
    _ = Real.exp ((24 / 25 : ℝ) * Real.exp L + 6 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (Real.exp L - D * L) := by
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_right (le_abs_self (D + 6)) hL
      linarith
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]

end Ostmann

end OAI
