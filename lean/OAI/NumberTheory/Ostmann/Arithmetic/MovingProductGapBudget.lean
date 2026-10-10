import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveProductBounds
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationTargets

namespace OAI

/-! # The recursive product budget is the prescribed compensation gap -/
namespace Ostmann

noncomputable def movingTargetPivotExponent (G : ℝ) (ws : List ℝ) (n : ℕ) : ℝ :=
  G + (2 : ℝ) ^ n * (ws.drop n).headD 0

private theorem drop_sum_head (ws : List ℝ) (n : ℕ) :
    (ws.drop n).sum = (ws.drop n).headD 0 + (ws.drop (n + 1)).sum := by
  induction ws generalizing n with
  | nil => simp
  | cons w ws ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [List.drop_succ_cons] using ih n

/-- With exact target centers, the product remaining at depth `n` is precisely
that of the protected slots and the as-yet unused compensation types. -/
theorem movingProductExponent_targets (G J : ℝ) (ws : List ℝ) (n : ℕ) :
    movingProductExponent (movingTargetPivotExponent G ws) (2 * G + J + ws.sum) n =
      2 * G + (2 : ℝ) ^ n * (J + (ws.drop n).sum) := by
  induction n with
  | zero => simp only [movingProductExponent, pow_zero, List.drop_zero, one_mul, add_assoc]
  | succ n ih =>
    rw [movingProductExponent, ih, movingTargetPivotExponent, pow_succ, drop_sum_head ws n]
    ring

private theorem target_drop_gap (J : ℝ) (ds : List ℝ) (n : ℕ) (hn : n < ds.length) :
    J + ((movingCompensationTargets J ds).drop (n + 1)).sum -
      ((movingCompensationTargets J ds).drop n).headD 0 = (ds.drop n).headD 0 := by
  induction ds generalizing n with
  | nil => simp at hn
  | cons d ds ih =>
    cases n with
    | zero => simp only [movingCompensationTargets, List.drop_zero, List.headD_cons,
        List.drop_succ_cons]; ring
    | succ n =>
      have hn' : n < ds.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hn
      simpa only [movingCompensationTargets, List.drop_succ_cons] using ih n hn'

/-- This is the exact gap from the manuscript's backwards recursion, expressed
in the product budget used by the integer-extended coefficients. -/
theorem movingProductExponent_target_gap (G J : ℝ) (ds : List ℝ)
    (n : ℕ) (hn : n < ds.length) :
    let ws := movingCompensationTargets J ds
    movingProductExponent (movingTargetPivotExponent G ws) (2 * G + J + ws.sum) n -
      2 * movingTargetPivotExponent G ws n = (2 : ℝ) ^ n * (ds.drop n).headD 0 := by
  dsimp only
  rw [movingProductExponent_targets, movingTargetPivotExponent, drop_sum_head]
  have hh := target_drop_gap J ds n hn
  linear_combination (2 : ℝ) ^ n * hh

/-- A finite center-rounding loss grows only linearly with the depth after
normalization by the number of leaves. -/
theorem movingProductExponent_rounding_bound (T U : ℕ → ℝ) (W Z C R : ℝ)
    (hW : W ≤ Z + C) (hTU : ∀ j, U j - (2 : ℝ) ^ j * R ≤ T j) (n : ℕ) :
    movingProductExponent T W n ≤ movingProductExponent U Z n +
      (2 : ℝ) ^ n * (C + n * R) := by
  induction n with
  | zero => simpa only [movingProductExponent, pow_zero, Nat.cast_zero, mul_zero,
      zero_mul, add_zero, one_mul] using hW
  | succ n ih =>
    rw [movingProductExponent, movingProductExponent, pow_succ, Nat.cast_add, Nat.cast_one]
    have hh := hTU n
    nlinarith only [ih, hh]

end Ostmann

end OAI
