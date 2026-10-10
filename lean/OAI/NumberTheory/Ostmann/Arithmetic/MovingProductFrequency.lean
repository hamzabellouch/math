import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveTemplateCaps
import OAI.NumberTheory.Ostmann.Arithmetic.MovingIntegerRanges

namespace OAI

/-! # Integer frequency cutoffs that retain the actual product-window center -/
namespace Ostmann

/-- Centering at the measured terminal product avoids charging its rounding
error again at each subsequent transfer. -/
noncomputable def movingProductFrequencyExponent (T : ℕ → ℝ)
    (W Y m : ℝ) (n : ℕ) : ℝ :=
  movingProductExponent T W n - Y + (2 : ℝ) ^ n * Real.sqrt (4 * m)

noncomputable def movingProductNaturalCutoff (T : ℕ → ℝ)
    (W Y m : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (movingProductFrequencyExponent T W Y m n)⌋₊

theorem movingProductExponent_monotone (T : ℕ → ℝ) (W : ℝ)
    (hgap : ∀ n, 2 * T n ≤ movingProductExponent T W n) :
    Monotone (movingProductExponent T W) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [movingProductExponent]
  linarith [hgap n]

theorem movingProductNaturalCutoff_monotone (T : ℕ → ℝ) (W Y m : ℝ)
    (hgap : ∀ n, 2 * T n ≤ movingProductExponent T W n) :
    Monotone (movingProductNaturalCutoff T W Y m) := by
  intro i j hij
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  have hE := movingProductExponent_monotone T W hgap hij
  have hpow : (2 : ℝ) ^ i ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hij
  have hs := mul_le_mul_of_nonneg_right hpow (Real.sqrt_nonneg (4 * m))
  dsimp only [movingProductFrequencyExponent]
  linarith

theorem movingProductFrequency_reserve (T : ℕ → ℝ) (W Y m : ℝ) (n : ℕ) :
    movingProductFrequencyExponent T W Y m (n + 1) -
      (movingProductFrequencyExponent T W Y m n + movingProductExponent T W n - 2 * T n) =
      (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  simp only [movingProductFrequencyExponent, movingProductExponent, pow_succ]
  ring

/-- The full ceiling product cap satisfies the next integer-frequency bound.
Only the actual lower bound on the inserted pivot product is needed. -/
theorem movingProductNaturalCutoff_scale (T : ℕ → ℝ) (W Y m : ℝ) (n : ℕ)
    (hm : 64 ≤ m) (hY : Y ≤ W)
    (hgap : ∀ j, 2 * T j ≤ movingProductExponent T W j)
    (hH : 0 ≤ movingProductExponent T W n - T n)
    (M : ℕ) (hM : Real.exp (T n) ≤ (M : ℝ)) :
    2 * movingProductNaturalCutoff T W Y m n *
        ⌈Real.exp (movingProductExponent T W n - T n)⌉₊ ≤
      movingProductNaturalCutoff T W Y m (n + 1) * M := by
  let E := movingProductExponent T W n
  let F := movingProductFrequencyExponent T W Y m n
  let F' := movingProductFrequencyExponent T W Y m (n + 1)
  have hroot : 8 ≤ Real.sqrt (4 * m) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hpow : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpow' : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog4 : Real.log (4 : ℝ) ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hE' : W ≤ movingProductExponent T W (n + 1) :=
    movingProductExponent_monotone T W hgap (Nat.zero_le _)
  have hF' : Real.log 2 ≤ F' := by
    dsimp only [F', movingProductFrequencyExponent]
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hreserve := movingProductFrequency_reserve T W Y m n
  have hmargin : Real.log 4 + F + E - T n ≤ F' + T n - Real.log 2 := by
    dsimp only [F, F', E] at *
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hHceil : (⌈Real.exp (E - T n)⌉₊ : ℝ) ≤ 2 * Real.exp (E - T n) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_pos (E - T n)).le).le
    have he := Real.one_le_exp hH
    dsimp only [E] at *
    linarith
  have hV : (movingProductNaturalCutoff T W Y m n : ℝ) ≤ Real.exp F :=
    Nat.floor_le (Real.exp_pos F).le
  have hV' : Real.exp F' / 2 ≤ (movingProductNaturalCutoff T W Y m (n + 1) : ℝ) := by
    have hh := (natural_exp_cutoff_bounds F' hF').2.2
    change Real.exp F' ≤ 2 * (movingProductNaturalCutoff T W Y m (n + 1) : ℝ) at hh
    linarith
  have hscaled : (2 : ℝ) * movingProductNaturalCutoff T W Y m n *
      (⌈Real.exp (E - T n)⌉₊ : ℝ) ≤
        (movingProductNaturalCutoff T W Y m (n + 1) : ℝ) * M := by
    calc
      _ ≤ (2 * Real.exp F) * (2 * Real.exp (E - T n)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hV (by norm_num)) hHceil
          (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (Real.log 4 + F + E - T n) := by
        rw [show Real.log 4 + F + E - T n = Real.log 4 + (F + (E - T n)) by ring,
          Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
        ring
      _ ≤ Real.exp (F' + T n - Real.log 2) := Real.exp_le_exp.mpr hmargin
      _ = (Real.exp F' / 2) * Real.exp (T n) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        ring
      _ ≤ _ := mul_le_mul hV' hM (Real.exp_nonneg _) (Nat.cast_nonneg _)
  exact_mod_cast hscaled

end Ostmann

end OAI
