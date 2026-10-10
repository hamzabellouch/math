import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.ZeroDensity.NonexceptionalRieszBound

namespace OAI

/-! # Exponential parameter choice for the Riesz contour

The height is `exp y`, the length is `exp (y²)` and the right abscissa is
`1 + 1/y²`.  Fixed polynomial losses are absorbed into a smaller decay rate.
-/

namespace Ostmann

open Filter Asymptotics

theorem riesz_polynomial_absorption (C d : ℝ) (hd : 0 < d) :
    ∀ᶠ y : ℝ in atTop, C * (y ^ 2 + 1) ≤ Real.exp (d * y) := by
  have hp := (isLittleO_pow_exp_pos_mul_atTop 2 hd).const_mul_left C
  have hc := (isLittleO_pow_exp_pos_mul_atTop 0 hd).const_mul_left C
  have hb := (hp.add hc).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with y hy
  have hh := (le_abs_self (C * y ^ 2 + C)).trans (by
    simpa only [pow_zero, mul_one, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), one_mul] using hy)
  nlinarith

theorem riesz_exponential_error (c A B E : ℝ) (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) :
    ∀ᶠ y : ℝ in atTop, ∀ H : ℝ, 0 < H → H ≤ 3 * y →
      A * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 - c / H) +
        B * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 +
        2 * (1 / ((1 + 1 / y ^ 2) - 1) + E) *
          (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
        3 * Real.exp (y ^ 2 - (c / 6) * y) := by
  let d := c / 6
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : 2 * d ≤ 1 := by dsimp [d]; linarith
  have hp1 := riesz_polynomial_absorption (9 * A) d hd
  have hp2 := riesz_polynomial_absorption (9 * B * Real.exp 1) d hd
  have hp3 := riesz_polynomial_absorption (2 * (1 + E) * Real.exp 1) d hd
  filter_upwards [hp1, hp2, hp3, eventually_ge_atTop (1 : ℝ)] with y hyA hyB hyE hy1
  intro H hH hHy
  have hy0 : 0 < y := by linarith
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy0.ne'
  have hH2 : H ^ 2 ≤ 9 * y ^ 2 := by nlinarith
  have h1 : A * H ^ 2 ≤ Real.exp (d * y) := by
    apply le_trans _ hyA
    nlinarith [mul_le_mul_of_nonneg_left hH2 hA]
  have h2 : B * H ^ 2 * Real.exp 1 ≤ Real.exp (d * y) := by
    apply le_trans _ hyB
    have he := Real.exp_pos (1 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hH2 (mul_nonneg hB he.le)]
  have h3 : 2 * (y ^ 2 + E) * Real.exp 1 ≤ Real.exp (d * y) := by
    apply le_trans _ hyE
    have he := Real.exp_pos (1 : ℝ)
    nlinarith [mul_nonneg hE (sq_nonneg y),
      mul_nonneg (mul_nonneg hE (sq_nonneg y)) he.le]
  have hrpow (r : ℝ) : (Real.exp (y ^ 2)) ^ r = Real.exp (y ^ 2 * r) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hr : (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) =
      Real.exp (y ^ 2) * Real.exp 1 := by
    rw [hrpow, show y ^ 2 * (1 + 1 / y ^ 2) = y ^ 2 + 1 by field_simp,
      Real.exp_add]
  have hgap : y ^ 2 * (1 - c / H) ≤ y ^ 2 - 2 * d * y := by
    have hh : c * y / 3 ≤ c / H * y ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hHy (show 0 ≤ c * y by positivity)
      rw [show c / H * y ^ 2 = c * y ^ 2 / H by ring]
      apply (le_div_iff₀ hH).mpr
      nlinarith
    dsimp [d]
    nlinarith
  have ht1 : A * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 - c / H) ≤
      Real.exp (y ^ 2 - d * y) := by
    rw [hrpow]
    calc
      _ ≤ Real.exp (d * y) * Real.exp (y ^ 2 - 2 * d * y) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr hgap) (by positivity) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have ht2 : B * H ^ 2 * (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / (Real.exp y) ^ 2 ≤
      Real.exp (y ^ 2 - d * y) := by
    rw [hr, ← Real.exp_nat_mul]
    calc
      _ = (B * H ^ 2 * Real.exp 1) * Real.exp (y ^ 2 - 2 * y) := by
        rw [Real.exp_sub]; ring_nf
      _ ≤ Real.exp (d * y) * Real.exp (y ^ 2 - 2 * y) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  have ht3 : 2 * (1 / ((1 + 1 / y ^ 2) - 1) + E) *
      (Real.exp (y ^ 2)) ^ (1 + 1 / y ^ 2) / Real.exp y ≤
      Real.exp (y ^ 2 - d * y) := by
    rw [hr, show 1 / ((1 + 1 / y ^ 2) - 1) = y ^ 2 by field_simp; ring]
    calc
      _ = (2 * (y ^ 2 + E) * Real.exp 1) * Real.exp (y ^ 2 - y) := by
        rw [Real.exp_sub]; ring
      _ ≤ Real.exp (d * y) * Real.exp (y ^ 2 - y) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith
  dsimp [d] at ht1 ht2 ht3
  linarith

end Ostmann

end OAI
