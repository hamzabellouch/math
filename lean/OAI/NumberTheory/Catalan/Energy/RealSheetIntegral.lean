import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.NumberTheory.Catalan.Estimates.RealCoordinateProduct
import OAI.NumberTheory.Catalan.Estimates.RealWeightedVandermonde

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial Set

theorem chebyshevT_eval_sheet (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    (Chebyshev.T ℤ (d : ℤ)).eval₂ (Int.castRingHom ℝ) ((x + x⁻¹) / 2) =
      (x ^ d + (x⁻¹) ^ d) / 2 := by
  induction d using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp
  | more d ih0 ih1 =>
    have hi1 : (d : ℤ) + 1 = ((d + 1 : ℕ) : ℤ) := by omega
    rw [Nat.cast_add, Nat.cast_ofNat, Chebyshev.T_add_two]
    simp only [eval₂_sub, eval₂_mul, eval₂_ofNat, eval₂_X]
    rw [hi1, ih1, ih0]
    simp only [pow_add, pow_one, pow_two]
    linear_combination (x ^ d + (x⁻¹) ^ d) / 2 * (mul_inv_cancel₀ hx)

theorem chebyshevU_eval_sheet (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ((x⁻¹ - x) / 2) *
        (Chebyshev.U ℤ ((d : ℤ) - 1)).eval₂ (Int.castRingHom ℝ)
          ((x + x⁻¹) / 2) =
      ((x⁻¹) ^ d - x ^ d) / 2 := by
  induction d using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more d ih0 ih1 =>
    have hi2 : ((d + 2 : ℕ) : ℤ) - 1 = (d : ℤ) + 1 := by omega
    have hi1 : ((d + 1 : ℕ) : ℤ) - 1 = (d : ℤ) := by omega
    rw [hi1] at ih1
    rw [hi2, Chebyshev.U_add_one]
    simp only [eval₂_sub, eval₂_mul, eval₂_ofNat, eval₂_X]
    calc
      _ = 2 * ((x + x⁻¹) / 2) *
            (((x⁻¹ - x) / 2) *
              (Chebyshev.U ℤ (d : ℤ)).eval₂ (Int.castRingHom ℝ) ((x + x⁻¹) / 2)) -
          ((x⁻¹ - x) / 2) *
            (Chebyshev.U ℤ ((d : ℤ) - 1)).eval₂ (Int.castRingHom ℝ)
              ((x + x⁻¹) / 2) := by ring
      _ = 2 * ((x + x⁻¹) / 2) * (((x⁻¹) ^ (d + 1) - x ^ (d + 1)) / 2) -
          ((x⁻¹) ^ d - x ^ d) / 2 := by rw [ih1, ih0]
      _ = _ := by
        simp only [pow_add, pow_one, pow_two]
        linear_combination ((x⁻¹) ^ d - x ^ d) / 2 * (mul_inv_cancel₀ hx)

theorem inv_realCoordinateInv {x : ℝ} (hx : x ≠ 0) :
    (realCoordinateInv x)⁻¹ = (x + x⁻¹) / 2 := by
  unfold realCoordinateInv
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hx]
  ring

theorem sqrt_div_realCoordinateInv {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x =
      (x⁻¹ - x) / 2 := by
  rw [sqrt_one_sub_realCoordinateInv_sq hx]
  unfold realCoordinateInv
  have hd : 1 + x ^ 2 ≠ 0 := by positivity
  field_simp [hx0]

theorem rowP_realCoordinateInv {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ≠ 0) :
    (realPoly (rowP N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        ((x ^ rowDistance N r + (x⁻¹) ^ rowDistance N r) / 2) := by
  have ht : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx) (by positivity)
  unfold realPoly
  rw [← eval₂_eq_eval_map, rowP_eval₂ (Int.castRingHom ℝ) hN hr ht,
    inv_realCoordinateInv hx, chebyshevT_eval_sheet _ hx]

theorem rowD_realCoordinateInv {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x *
        (realPoly (rowD N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (Int.sign (rowOffset N r) : ℝ) *
          (((x⁻¹) ^ rowDistance N r - x ^ rowDistance N r) / 2) := by
  have ht : realCoordinateInv x ≠ 0 := by
    unfold realCoordinateInv
    exact div_ne_zero (mul_ne_zero (by norm_num) hx0) (by positivity)
  unfold realPoly
  rw [sqrt_div_realCoordinateInv hx hx0, ← eval₂_eq_eval_map,
    rowD_eval₂ (Int.castRingHom ℝ) hN hr ht, inv_realCoordinateInv hx0]
  calc
    _ = (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (Int.sign (rowOffset N r) : ℝ) *
          (((x⁻¹ - x) / 2) *
            (Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1)).eval₂ (Int.castRingHom ℝ)
              ((x + x⁻¹) / 2)) := by
      rw [show (Int.castRingHom ℝ) (Int.sign (rowOffset N r)) =
        (Int.sign (rowOffset N r) : ℝ) from rfl]
      ring
    _ = _ := by rw [chebyshevU_eval_sheet _ hx0]

private theorem sheet_natAbs_sum (m : ℤ) (x : ℝ) :
    x ^ m.natAbs + (x⁻¹) ^ m.natAbs = x ^ m + x ^ (-m) := by
  calc
    _ = x ^ (m.natAbs : ℤ) + x ^ (-(m.natAbs : ℤ)) := by
      simp only [zpow_neg, zpow_natCast, inv_pow]
    _ = _ := by
      rcases Int.natAbs_eq m with hm | hm
      · exact congrArg (fun z : ℤ => x ^ z + x ^ (-z)) hm.symm
      · calc
          _ = x ^ (-(m.natAbs : ℤ)) + x ^ (-(-(m.natAbs : ℤ))) := by
            rw [neg_neg]
            ring
          _ = _ := congrArg (fun z : ℤ => x ^ z + x ^ (-z)) hm.symm

private theorem sheet_natAbs_difference (m : ℤ) (x : ℝ) :
    (Int.sign m : ℝ) * ((x⁻¹) ^ m.natAbs - x ^ m.natAbs) =
      x ^ (-m) - x ^ m := by
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [Int.sign_eq_neg_one_of_neg hm]
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
    calc
      _ = x ^ (m.natAbs : ℤ) - x ^ (-(m.natAbs : ℤ)) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
        ring
      _ = _ := by rw [Int.ofNat_natAbs_of_nonpos hm.le, neg_neg]
  · subst m
    simp
  · rw [Int.sign_eq_one_of_pos hm]
    simp only [Int.cast_one, one_mul]
    calc
      _ = x ^ (-(m.natAbs : ℤ)) - x ^ (m.natAbs : ℤ) := by
        simp only [zpow_neg, zpow_natCast, inv_pow]
      _ = _ := by rw [Int.natAbs_of_nonneg hm.le]

theorem rowP_realCoordinateInv_signed {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ≠ 0) :
    (realPoly (rowP N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        ((x ^ rowOffset N r + x ^ (-rowOffset N r)) / 2) := by
  simpa only [rowDistance, sheet_natAbs_sum] using rowP_realCoordinateInv hN hr hx

theorem rowD_realCoordinateInv_signed {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    Real.sqrt (1 - realCoordinateInv x ^ 2) / realCoordinateInv x *
        (realPoly (rowD N r)).eval (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        ((x ^ (-rowOffset N r) - x ^ rowOffset N r) / 2) := by
  rw [rowD_realCoordinateInv hN hr hx hx0]
  calc
    _ = (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (((Int.sign (rowOffset N r) : ℝ) *
          ((x⁻¹) ^ rowDistance N r - x ^ rowDistance N r)) / 2) := by ring
    _ = _ := by rw [rowDistance, sheet_natAbs_difference]

theorem realRowAmplitude_sheet {N r : ℕ} (hN : 0 < N) (hr : r < n N)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    realRowAmplitude N r (realCoordinateInv x) =
      (1 - realCoordinateInv x) ^ h N * realCoordinateInv x ^ (Cdegree N - 1) *
        (if x < 0 then
          (1 / 2 : ℝ) * x ^ (-rowOffset N r) + (1 / 2 : ℝ) * x ^ rowOffset N r
        else
          -(1 / 4 : ℝ) * x ^ (-rowOffset N r) + (5 / 4 : ℝ) * x ^ rowOffset N r) := by
  by_cases hn : x < 0
  · have ht : realCoordinateInv x < 0 := by
      unfold realCoordinateInv
      exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hn) (by positivity)
    rw [realRowAmplitude_of_neg N r ht, rowP_realCoordinateInv_signed hN hr hx0, ite_eq_left hn]
    ring
  · have hp : 0 < x := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx0)
    have ht : 0 < realCoordinateInv x := by
      unfold realCoordinateInv
      exact div_pos (mul_pos (by norm_num) hp) (by positivity)
    rw [realRowAmplitude_of_pos N r ht, rowP_realCoordinateInv_signed hN hr hx0,
      rowD_realCoordinateInv_signed hN hr hx hx0, ite_eq_right hn]
    ring

end

section

open Set
open scoped BigOperators

def realSheetDeterminant (N : ℕ) (x : Fin (n N) → ℝ) : ℝ :=
  Matrix.det (Matrix.of (fun r i : Fin (n N) =>
    if x i < 0 then
      (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
    else
      -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val))

theorem realRowAmplitude_det_eq_sheet {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    Matrix.det (Matrix.of (fun r i : Fin (n N) =>
      realRowAmplitude N r.val (realCoordinateInv (x i)))) =
        realSheetDeterminant N x *
          ∏ i : Fin (n N), realCoordinateInv (x i) ^ (Cdegree N - 1) *
            (1 - realCoordinateInv (x i)) ^ h N := by
  classical
  let weight : Fin (n N) → ℝ := fun i =>
    realCoordinateInv (x i) ^ (Cdegree N - 1) * (1 - realCoordinateInv (x i)) ^ h N
  let A : Matrix (Fin (n N)) (Fin (n N)) ℝ := Matrix.of (fun r i =>
    if x i < 0 then
      (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
    else
      -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
        (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val)
  have hmatrix :
      Matrix.of (fun r i : Fin (n N) => realRowAmplitude N r.val (realCoordinateInv (x i))) =
        Matrix.of (fun r i : Fin (n N) => weight i * A r i) := by
    funext r i
    change realRowAmplitude N r.val (realCoordinateInv (x i)) = weight i * A r i
    rw [realRowAmplitude_sheet hN r.isLt (hx i) (hx0 i)]
    dsimp only [weight, A, Matrix.of_apply]
    ring
  rw [hmatrix, Matrix.det_mul_row]
  change (∏ i : Fin (n N), weight i) * realSheetDeterminant N x =
    realSheetDeterminant N x * (∏ i : Fin (n N), weight i)
  exact mul_comm _ _

end

section

open scoped BigOperators

def realFirstSheetMixedMatrix (N : ℕ) (x : Fin (n N) → ℝ) :
    Matrix (Fin (n N)) (Fin (n N)) ℝ :=
  Matrix.of (fun r i =>
    (x i) ^ r.rev.val +
      (if x i < 0 then (x i) ^ (n N - 1 - 2 * g N)
        else -5 * (x i) ^ (n N - 1 - 2 * g N)) * (x i) ^ r.val)

theorem realFirstSheet_far_monomial {N : ℕ} (hN : 0 < N)
    (r : Fin (n N)) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) * x ^ r.rev.val =
      x ^ (-rowOffset N r.val) := by
  calc
    _ = x ^ (((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) + (r.rev.val : ℤ)) := by
      rw [zpow_add₀ hx, zpow_natCast]
    _ = x ^ (-rowOffset N r.val) := by
      congr 1
      have hr := r.isLt
      simp only [Fin.val_rev]
      unfold rowOffset n g at *
      omega

theorem realFirstSheet_near_monomial {N : ℕ} (hN : 0 < N)
    (r : Fin (n N)) {x : ℝ} (hx : x ≠ 0) :
    x ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) *
        (x ^ (n N - 1 - 2 * g N) * x ^ r.val) =
      x ^ rowOffset N r.val := by
  calc
    _ = x ^ ((((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) +
        ((n N - 1 - 2 * g N : ℕ) : ℤ)) + (r.val : ℤ)) := by
      simp only [zpow_add₀ hx, zpow_natCast]
      ring
    _ = x ^ rowOffset N r.val := by
      congr 1
      unfold rowOffset n g
      omega

theorem realFirstSheet_entry_factor {N : ℕ} (hN : 0 < N)
    (r : Fin (n N)) {x : ℝ} (hx : x ≠ 0) :
    (if x < 0 then
      (1 / 2 : ℝ) * x ^ (-rowOffset N r.val) +
        (1 / 2 : ℝ) * x ^ rowOffset N r.val
    else
      -(1 / 4 : ℝ) * x ^ (-rowOffset N r.val) +
        (5 / 4 : ℝ) * x ^ rowOffset N r.val) =
      (if x < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
        x ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) *
          (x ^ r.rev.val +
            (if x < 0 then x ^ (n N - 1 - 2 * g N)
              else -5 * x ^ (n N - 1 - 2 * g N)) * x ^ r.val) := by
  by_cases hneg : x < 0
  · simp only [ite_eq_left hneg]
    rw [← realFirstSheet_far_monomial hN r hx,
      ← realFirstSheet_near_monomial hN r hx]
    ring
  · simp only [ite_eq_right hneg]
    rw [← realFirstSheet_far_monomial hN r hx,
      ← realFirstSheet_near_monomial hN r hx]
    ring

theorem realSheetDeterminant_firstSheet_factor {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ≠ 0) :
    realSheetDeterminant N x =
      (∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
        (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
          Matrix.det (realFirstSheetMixedMatrix N x) := by
  classical
  unfold realSheetDeterminant
  have hmatrix :
      Matrix.of (fun r i : Fin (n N) =>
        if x i < 0 then
          (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
        else
          -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val) =
        Matrix.of (fun r i : Fin (n N) =>
          ((if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
            (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
              realFirstSheetMixedMatrix N x r i) := by
    ext r i
    exact realFirstSheet_entry_factor hN r (hx i)
  rw [hmatrix, Matrix.det_mul_row]

theorem realFirstSheet_far_coefficient_abs_le (x : ℝ) :
    |if x < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)| ≤ 1 := by
  by_cases hx : x < 0 <;> norm_num [hx]

theorem realFirstSheet_factor_abs_le (N : ℕ) (x : Fin (n N) → ℝ) :
    |∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
      (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| ≤
        ∏ i, |(x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod₀
  · intro i _
    exact abs_nonneg _
  · intro i _
    rw [abs_mul]
    calc
      _ ≤ 1 * |(x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| :=
        mul_le_mul_of_nonneg_right (realFirstSheet_far_coefficient_abs_le (x i))
          (abs_nonneg _)
      _ = _ := one_mul _

theorem realFirstSheet_factor_abs_le_weight (N : ℕ) (x : Fin (n N) → ℝ) :
    |∏ i, (if x i < 0 then (1 / 2 : ℝ) else -(1 / 4 : ℝ)) *
      (x i) ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))| ≤
        ∏ i, |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  simpa only [abs_zpow] using realFirstSheet_factor_abs_le N x

theorem realSheetDeterminant_abs_le_firstSheet_mixed {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ≠ 0) :
    |realSheetDeterminant N x| ≤
      (∏ i, |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) *
        |Matrix.det (realFirstSheetMixedMatrix N x)| := by
  rw [realSheetDeterminant_firstSheet_factor hN x hx, abs_mul]
  exact mul_le_mul_of_nonneg_right (realFirstSheet_factor_abs_le_weight N x)
    (abs_nonneg _)

end

section

open Set

section

private theorem sqrt_one_add_inv_sq {x : ℝ} (hx0 : x ≠ 0) :
    Real.sqrt (1 + (x⁻¹) ^ 2) = Real.sqrt (1 + x ^ 2) / |x| := by
  have heq : 1 + (x⁻¹) ^ 2 = (1 + x ^ 2) / x ^ 2 := by
    field_simp [hx0]
    ring
  rw [heq, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs]

theorem sheet_far_weight_eq (N : ℕ) {x : ℝ} (hx0 : x ≠ 0) :
    |(x⁻¹) ^ (-(g N : ℤ))| * Real.sqrt (1 + (x⁻¹) ^ 2) ^ (n N - 1) =
      Real.sqrt (1 + x ^ 2) ^ (n N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  rw [abs_zpow, abs_inv, sqrt_one_add_inv_sq hx0]
  simp only [zpow_neg, zpow_natCast, inv_pow, inv_inv, div_pow]
  rw [zpow_sub₀ (abs_ne_zero.mpr hx0)]
  simp only [zpow_natCast]
  ring

theorem sheet_near_weight_le {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    |x ^ (-(g N : ℤ))| * Real.sqrt (1 + x ^ 2) ^ (n N - 1) ≤
      Real.sqrt (1 + x ^ 2) ^ (n N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  have hdim : 2 * g N ≤ n N - 1 := by
    unfold g n
    omega
  have hexp : (g N : ℤ) - ((n N - 1 : ℕ) : ℤ) ≤ -(g N : ℤ) := by omega
  have hp := zpow_le_zpow_right_of_le_one₀ (abs_pos.mpr hx0)
    (abs_lt.mpr hx).le hexp
  rw [abs_zpow, mul_comm]
  exact mul_le_mul_of_nonneg_left hp (pow_nonneg (Real.sqrt_nonneg _) _)

theorem sheet_choice_weight_le {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) (ε : Bool) :
    let z := if ε then x else x⁻¹
    |z ^ (-(g N : ℤ))| * Real.sqrt (1 + z ^ 2) ^ (n N - 1) ≤
      Real.sqrt (1 + x ^ 2) ^ (n N - 1) *
        |x| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)) := by
  cases ε
  · simpa using (sheet_far_weight_eq N hx0).le
  · simpa using sheet_near_weight_le hN hx hx0

end

open Set
open scoped BigOperators

def realSheetCoefficient (x : ℝ) (near : Bool) : ℝ :=
  if x < 0 then 1 / 2 else if near then 5 / 4 else -(1 / 4)

def realSheetNode (x : ℝ) (near : Bool) : ℝ :=
  if near then x else x⁻¹

theorem det_column_sum_bool {m : ℕ}
    (A : Bool → Matrix (Fin m) (Fin m) ℝ) :
    Matrix.det (Matrix.of (fun r i : Fin m => ∑ b : Bool, A b r i)) =
      ∑ ε : Fin m → Bool,
        Matrix.det (Matrix.of (fun r i : Fin m => A (ε i) r i)) := by
  classical
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]

theorem realSheetDeterminant_eq_sum (N : ℕ) (x : Fin (n N) → ℝ) :
    realSheetDeterminant N x =
      ∑ ε : Fin (n N) → Bool,
        (∏ i, realSheetCoefficient (x i) (ε i)) *
          Matrix.det (Matrix.of (fun r i : Fin (n N) =>
            realSheetNode (x i) (ε i) ^ rowOffset N r.val)) := by
  classical
  have hmatrix :
      Matrix.of (fun r i : Fin (n N) =>
        if x i < 0 then
          (1 / 2 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (1 / 2 : ℝ) * (x i) ^ rowOffset N r.val
        else
          -(1 / 4 : ℝ) * (x i) ^ (-rowOffset N r.val) +
            (5 / 4 : ℝ) * (x i) ^ rowOffset N r.val) =
        Matrix.of (fun r i : Fin (n N) => ∑ b : Bool,
          realSheetCoefficient (x i) b *
            realSheetNode (x i) b ^ rowOffset N r.val) := by
    ext r i
    by_cases hi : x i < 0 <;>
      simp [realSheetCoefficient, realSheetNode, hi, zpow_neg] <;> ring
  unfold realSheetDeterminant
  rw [hmatrix]
  have hexpand := det_column_sum_bool (fun b => Matrix.of (fun r i : Fin (n N) =>
    realSheetCoefficient (x i) b * realSheetNode (x i) b ^ rowOffset N r.val))
  simp only [Matrix.of_apply] at hexpand
  rw [hexpand]
  apply Finset.sum_congr rfl
  intro ε _
  simpa only [Matrix.of_apply] using
    Matrix.det_mul_row (fun i => realSheetCoefficient (x i) (ε i))
      (Matrix.of (fun r i : Fin (n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset N r.val))

theorem realSheetCoefficient_abs_sum_le (x : ℝ) :
    (∑ b : Bool, |realSheetCoefficient x b|) ≤ (3 / 2 : ℝ) := by
  by_cases hx : x < 0 <;>
    norm_num [realSheetCoefficient, hx, Fintype.sum_bool]

theorem realSheetCoefficient_sum_abs_prod_le (N : ℕ) (x : Fin (n N) → ℝ) :
    (∑ ε : Fin (n N) → Bool,
      |∏ i, realSheetCoefficient (x i) (ε i)|) ≤ (3 / 2 : ℝ) ^ n N := by
  classical
  calc
    _ = ∏ i, ∑ b : Bool, |realSheetCoefficient (x i) b| := by
      simp only [Finset.abs_prod]
      exact (Fintype.prod_sum (fun i b => |realSheetCoefficient (x i) b|)).symm
    _ ≤ ∏ _i : Fin (n N), (3 / 2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      · intro i _
        exact realSheetCoefficient_abs_sum_le (x i)
    _ = (3 / 2 : ℝ) ^ n N := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem laurent_monomial_det_eq {m : ℕ} (g : ℕ) (z : Fin m → ℝ)
    (hz : ∀ i, z i ≠ 0) :
    Matrix.det (Matrix.of (fun r i : Fin m => z i ^ ((r.val : ℤ) - (g : ℤ)))) =
      (∏ i, z i ^ (-(g : ℤ))) * Matrix.det (Matrix.vandermonde z) := by
  have hmatrix :
      Matrix.of (fun r i : Fin m => z i ^ ((r.val : ℤ) - (g : ℤ))) =
        Matrix.of (fun r i : Fin m =>
          z i ^ (-(g : ℤ)) * (Matrix.vandermonde z).transpose r i) := by
    ext r i
    simp only [Matrix.of_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      sub_eq_add_neg, zpow_add₀ (hz i), zpow_natCast]
    ring
  rw [hmatrix, Matrix.det_mul_row, Matrix.det_transpose]

theorem laurent_monomial_det_abs_le {m : ℕ} (g : ℕ) (z : Fin m → ℝ)
    (hz : ∀ i, z i ≠ 0) :
    |Matrix.det (Matrix.of (fun r i : Fin m => z i ^ ((r.val : ℤ) - (g : ℤ))))| ≤
      (Real.sqrt (m : ℝ)) ^ m / (2 : ℝ) ^ (m.choose 2) *
        ∏ i, (|z i ^ (-(g : ℤ))| * Real.sqrt (1 + z i ^ 2) ^ (m - 1)) := by
  rw [laurent_monomial_det_eq g z hz, abs_mul, Finset.abs_prod, Matrix.det_vandermonde]
  calc
    _ ≤ (∏ i, |z i ^ (-(g : ℤ))|) *
        ((Real.sqrt (m : ℝ)) ^ m / (2 : ℝ) ^ (m.choose 2) *
          ∏ i, Real.sqrt (1 + z i ^ 2) ^ (m - 1)) :=
      mul_le_mul_of_nonneg_left (weighted_real_vandermonde_le_sqrt z)
        (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      ring

theorem realSheetDeterminant_abs_le_of_monomial_bound (N : ℕ)
    (x : Fin (n N) → ℝ) (B : ℝ)
    (hB : ∀ ε : Fin (n N) → Bool,
      |Matrix.det (Matrix.of (fun r i : Fin (n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset N r.val))| ≤ B) :
    |realSheetDeterminant N x| ≤ (3 / 2 : ℝ) ^ n N * B := by
  classical
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => false))
  rw [realSheetDeterminant_eq_sum]
  calc
    _ ≤ ∑ ε : Fin (n N) → Bool,
        |(∏ i, realSheetCoefficient (x i) (ε i)) *
          Matrix.det (Matrix.of (fun r i : Fin (n N) =>
            realSheetNode (x i) (ε i) ^ rowOffset N r.val))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ε : Fin (n N) → Bool,
        |∏ i, realSheetCoefficient (x i) (ε i)| * B := by
      apply Finset.sum_le_sum
      intro ε _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB ε) (abs_nonneg _)
    _ = (∑ ε : Fin (n N) → Bool,
        |∏ i, realSheetCoefficient (x i) (ε i)|) * B := by rw [Finset.sum_mul]
    _ ≤ (3 / 2 : ℝ) ^ n N * B :=
      mul_le_mul_of_nonneg_right (realSheetCoefficient_sum_abs_prod_le N x) hB0

theorem realSheetDeterminant_abs_le_sqrt {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    |realSheetDeterminant N x| ≤
      (3 / 2 : ℝ) ^ n N * (Real.sqrt (n N : ℝ)) ^ n N /
        (2 : ℝ) ^ ((n N).choose 2) *
        ∏ i, (Real.sqrt (1 + x i ^ 2) ^ (n N - 1) *
          |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))) := by
  classical
  let C : ℝ := (Real.sqrt (n N : ℝ)) ^ n N / (2 : ℝ) ^ ((n N).choose 2)
  let W : Fin (n N) → ℝ := fun i =>
    Real.sqrt (1 + x i ^ 2) ^ (n N - 1) *
      |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ))
  have hchoice (ε : Fin (n N) → Bool) :
      |Matrix.det (Matrix.of (fun r i : Fin (n N) =>
        realSheetNode (x i) (ε i) ^ rowOffset N r.val))| ≤ C * ∏ i, W i := by
    let z : Fin (n N) → ℝ := fun i => realSheetNode (x i) (ε i)
    have hz (i : Fin (n N)) : z i ≠ 0 := by
      dsimp only [z, realSheetNode]
      split_ifs
      · exact hx0 i
      · exact inv_ne_zero (hx0 i)
    have hmon := laurent_monomial_det_abs_le (g N) z hz
    change |Matrix.det (Matrix.of (fun r i : Fin (n N) =>
      z i ^ ((r.val : ℤ) - (g N : ℤ))))| ≤ C * ∏ i, W i
    apply hmon.trans
    apply mul_le_mul_of_nonneg_left
    · apply Finset.prod_le_prod₀
      · intro i _
        exact mul_nonneg (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
      · intro i _
        simpa only [z, realSheetNode, W] using
          sheet_choice_weight_le hN (hx i) (hx0 i) (ε i)
    · positivity
  have h := realSheetDeterminant_abs_le_of_monomial_bound N x (C * ∏ i, W i) hchoice
  calc
    |realSheetDeterminant N x| ≤ (3 / 2 : ℝ) ^ n N * (C * ∏ i, W i) := h
    _ = _ := by dsimp only [C, W]; ring

end

section

open Set
open scoped BigOperators

theorem realSheetDeterminant_abs_le {N : ℕ} (hN : 0 < N)
    (x : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    |realSheetDeterminant N x| ≤
      (3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2) /
        (2 : ℝ) ^ ((n N).choose 2) *
        (∏ i : Fin (n N),
          ((1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) *
            |x i| ^ ((g N : ℤ) - ((n N - 1 : ℕ) : ℤ)))) := by
  have hdim : 1 ≤ n N := by unfold n; omega
  have hcast : ((n N - 1 : ℕ) : ℝ) = (n N : ℝ) - 1 := by
    rw [Nat.cast_sub hdim, Nat.cast_one]
  have hhead : Real.sqrt (n N : ℝ) ^ n N = (n N : ℝ) ^ ((n N : ℝ) / 2) := by
    symm
    simpa only [Real.rpow_natCast] using
      Real.rpow_div_two_eq_sqrt (n N : ℝ) (Nat.cast_nonneg (n N))
  have hrow (i : Fin (n N)) :
      Real.sqrt (1 + x i ^ 2) ^ (n N - 1) =
        (1 + x i ^ 2) ^ (((n N : ℝ) - 1) / 2) := by
    symm
    have h := Real.rpow_div_two_eq_sqrt ((n N - 1 : ℕ) : ℝ)
      (by positivity : (0 : ℝ) ≤ 1 + x i ^ 2)
    rw [Real.rpow_natCast] at h
    simpa only [hcast] using h
  simpa only [hhead, hrow] using realSheetDeterminant_abs_le_sqrt hN x hx hx0

end

open MeasureTheory Set
open scoped BigOperators

def sheetRealIntegrand (N : ℕ) (x s : Fin (n N) → ℝ) : ℝ :=
  realSheetDeterminant N x *
    (∏ i : Fin (n N), realCoordinateInv (x i) ^ (Cdegree N - 1) *
      (1 - realCoordinateInv (x i)) ^ h N) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i,
      (realCoordinateInv (x j) - realCoordinateInv (x i))) *
    (∏ i : Fin (n N), ∏ j ∈ Finset.Ioi i, (s j - s i)) ^ 2 *
    (∏ j : Fin (n N), (s j) ^ b N * (1 - s j) ^ q N) /
    (∏ i : Fin (n N), ∏ j : Fin (n N), (1 - realCoordinateInv (x i) * s j))

theorem coordinate_productRealIntegrand_eq_sheet {N : ℕ} (hN : 0 < N)
    (x s : Fin (n N) → ℝ) (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1)
    (hx0 : ∀ i, x i ≠ 0) :
    productRealIntegrand N (fun i => realCoordinateInv (x i)) s =
      sheetRealIntegrand N x s := by
  unfold productRealIntegrand sheetRealIntegrand
  rw [realRowAmplitude_det_eq_sheet hN x hx hx0]

theorem ae_coordinate_productRealIntegrand_eq_sheet {N : ℕ} (hN : 0 < N) :
    (fun p => productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2)
      =ᵐ[realCoordinateListPairMeasure N] (fun p => sheetRealIntegrand N p.1 p.2) := by
  have hreg : ∀ᵐ p ∂realCoordinateListPairMeasure N,
      ∀ i, p.1 i ∈ Ioo (-1 : ℝ) 1 ∧ p.1 i ≠ 0 := by
    exact (Measure.quasiMeasurePreserving_fst
      (μ := Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure))
      (ν := Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))).tendsto_ae.eventually
        (ae_realCoordinate_list_regular N)
  filter_upwards [hreg] with p hp
  exact coordinate_productRealIntegrand_eq_sheet hN p.1 p.2
    (fun i => (hp i).1) (fun i => (hp i).2)

theorem integrable_sheetRealIntegrand {N : ℕ} (hN : 0 < N) :
    Integrable (fun p => sheetRealIntegrand N p.1 p.2)
      (realCoordinateListPairMeasure N) :=
  (integrable_coordinate_productRealIntegrand N).congr
    (ae_coordinate_productRealIntegrand_eq_sheet hN)

theorem determinant_eq_sheetRealIntegral {N : ℕ} (hN : 0 < N) :
    determinant N = 1 / (((n N).factorial : ℝ) ^ 2) *
      ∫ x, (∫ s, sheetRealIntegrand N x s
        ∂Measure.pi (fun _ : Fin (n N) => volume.restrict (Ioo (0 : ℝ) 1)))
        ∂Measure.pi (fun _ : Fin (n N) => realCoordinateMeasure) := by
  rw [determinant_eq_coordinateProductIntegral N]
  congr 1
  calc
    _ = ∫ p, productRealIntegrand N (fun i => realCoordinateInv (p.1 i)) p.2
        ∂realCoordinateListPairMeasure N :=
      (integral_prod _ (integrable_coordinate_productRealIntegrand N)).symm
    _ = ∫ p, sheetRealIntegrand N p.1 p.2 ∂realCoordinateListPairMeasure N :=
      integral_congr_ae (ae_coordinate_productRealIntegrand_eq_sheet hN)
    _ = _ := integral_prod _ (integrable_sheetRealIntegrand hN)

end InternalCatalan

end

end OAI
