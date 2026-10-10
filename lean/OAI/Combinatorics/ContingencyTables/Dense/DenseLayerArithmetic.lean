import OAI.Combinatorics.ContingencyTables.Dense.DenseMixing
import Mathlib.Algebra.Order.Field.GeomSum

namespace OAI

/-! # Numerical finite-layer sum for dense rejection -/

namespace ContingencyTables.DenseAffine

open scoped BigOperators

theorem dense_layer_sum (d : ℕ) (hd : 14 ≤ d) (N : ℕ) :
    4 * (∑ j ∈ Finset.range N, (2 : ℝ) ^ (-(j : ℝ)) *
      Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4))) ≤ 16 := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  let a := 2 / (d : ℝ) ^ 2
  let b := 2 / (d : ℝ) ^ 5
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have htwo : (16 : ℝ) ≤ (d : ℝ) ^ 2 := by
    exact_mod_cast (show 16 ≤ d ^ 2 from
      (by norm_num : 16 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left (by omega : 4 ≤ d) 2))
  have hfive : (16 : ℝ) ≤ (d : ℝ) ^ 5 := by
    exact_mod_cast (show 16 ≤ d ^ 5 from
      (by norm_num : 16 ≤ 4 ^ 5).trans (Nat.pow_le_pow_left (by omega : 4 ≤ d) 5))
  have ha₈ : a ≤ 1 / 8 := by
    dsimp [a]
    apply (div_le_iff₀ (pow_pos hd₀ 2)).mpr
    nlinarith
  have hb₈ : b ≤ 1 / 8 := by
    dsimp [b]
    apply (div_le_iff₀ (pow_pos hd₀ 5)).mpr
    nlinarith
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
    norm_num at h ⊢
    exact h
  have hexp : Real.exp (a + b) ≤ 4 / 3 :=
    (Real.exp_le_exp.mpr (by linarith : a + b ≤ 1 / 4)).trans hquarter
  have hratio : Real.exp a / 2 ≤ 2 / 3 := by
    have h := (Real.exp_le_exp.mpr (by linarith : a ≤ 1 / 4)).trans hquarter
    linarith
  have hterm (j : ℕ) : (2 : ℝ) ^ (-(j : ℝ)) *
      Real.exp (2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4)) ≤
      (4 / 3 : ℝ) * (2 / 3 : ℝ) ^ j := by
    have heq : 2 * (d : ℝ) ^ 2 * ((d : ℝ) / (d : ℝ) ^ 8 + ((j : ℝ) + 1) / (d : ℝ) ^ 4) =
        (a + b) + (j : ℝ) * a := by
      dsimp [a, b]
      field_simp
      ring
    calc
      _ = Real.exp (a + b) * (Real.exp a / 2) ^ j := by
        rw [heq, Real.exp_add, Real.exp_nat_mul, Real.rpow_neg (by norm_num), Real.rpow_natCast,
          div_pow]
        ring
      _ ≤ _ := mul_le_mul hexp (pow_le_pow_left₀ (by positivity) hratio j)
        (by positivity) (by norm_num)
  have hgeom : (∑ j ∈ Finset.range N, (2 / 3 : ℝ) ^ j) ≤ 3 := by
    have h := geom_sum_mul_neg (2 / 3 : ℝ) N
    have hp : 0 ≤ (2 / 3 : ℝ) ^ N := by positivity
    nlinarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hterm j)
  rw [← Finset.mul_sum] at hsum
  nlinarith

end ContingencyTables.DenseAffine

end OAI
