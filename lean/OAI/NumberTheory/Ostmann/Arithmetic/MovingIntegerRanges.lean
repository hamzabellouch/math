import OAI.NumberTheory.Ostmann.Arithmetic.MovingCutoffReserve

namespace OAI

/-! # Rounded integer ranges for the actual moving-giant cutoffs -/

namespace Ostmann
open Filter
open scoped BigOperators

theorem movingCutoffExponent_ge_reserve (Bs BD Bz z m : ℝ) (n : ℕ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (hm : 0 ≤ m) :
    (2 : ℝ) ^ n * Real.sqrt (4 * m) ≤ movingCutoffExponent Bs BD Bz z m n := by
  have hlogz := Real.log_nonneg hz
  have hs : 0 ≤ ∑ j ∈ Finset.range n, spectatorStepGap BD Bz z ((2 : ℝ) ^ j) m := by
    apply Finset.sum_nonneg
    intro j _
    have hl := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ j)
    unfold spectatorStepGap
    positivity
  have hb : 0 ≤ spectatorBaseGap Bs z m := by unfold spectatorBaseGap; positivity
  unfold movingCutoffExponent
  linarith

/-- The same concrete floor cutoffs give both strict determinant rigidity
and the next-frequency bound, simultaneously at every transfer depth. -/
theorem eventually_moving_integer_ranges (Bs BD Bz z C : ℝ)
    (hBs : 0 ≤ Bs) (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz) (hz : 1 ≤ z) :
    ∀ᶠ m : ℝ in atTop, ∀ n : ℕ, ∀ T : ℝ, ∀ M R : ℕ,
      Real.exp (T - C) ≤ M →
      Real.exp (T + spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m - C) ≤ R →
      2 * naturalProductCap (T + C) * movingNaturalCutoff Bs BD Bz z m n < R ∧
      2 * movingNaturalCutoff Bs BD Bz z m n *
        naturalProductCap (T + spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m + C) ≤
        movingNaturalCutoff Bs BD Bz z m (n + 1) * M := by
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    eventually_gt_atTop ((20 / 3 : ℝ) * (Real.log 2 + 2 * C)),
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop (Real.log 4 + 2 * C))]
    with m hm hlinear hsqrt
  intro n T M R hM hR
  have hm0 : 0 ≤ m := by linarith
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hdiag := movingCutoff_diagonal_reserve Bs BD Bz z m hBD hBz hz hm n
  have hgap : Real.log 2 + 2 * C <
      spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m - movingCutoffExponent Bs BD Bz z m n := by
    nlinarith [mul_le_mul_of_nonneg_right hr hm0]
  have hs4 : Real.sqrt m ≤ Real.sqrt (4 * m) := Real.sqrt_le_sqrt (by linarith)
  have hnext : Real.log 4 + 2 * C <
      movingCutoffExponent Bs BD Bz z m (n + 1) -
        (movingCutoffExponent Bs BD Bz z m n + spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m) := by
    rw [movingCutoff_frequency_reserve]
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hlog2 : Real.log 2 ≤ movingCutoffExponent Bs BD Bz z m (n + 1) := by
    have he := movingCutoffExponent_ge_reserve Bs BD Bz z m (n + 1) hBs
      (by linarith) (by linarith) hz hm0
    have hr' : 1 ≤ (2 : ℝ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    have hroot : 1 ≤ Real.sqrt (4 * m) := Real.le_sqrt_of_sq_le (by nlinarith)
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hfloor (a : ℝ) : (naturalProductCap a : ℝ) ≤ Real.exp a :=
    Nat.floor_le (Real.exp_pos _).le
  have hV : (movingNaturalCutoff Bs BD Bz z m n : ℝ) ≤
      Real.exp (movingCutoffExponent Bs BD Bz z m n) := Nat.floor_le (Real.exp_pos _).le
  have hVnext := (natural_exp_cutoff_bounds (movingCutoffExponent Bs BD Bz z m (n + 1)) hlog2).2.2
  constructor
  · exact transfer_integer_rigidity_gap _ _ R T _ _ C (hfloor _) hV hR hgap
  · exact transfer_integer_frequency_cutoff M _ _ _ T _ _ _ C hM (hfloor _) hV hVnext
      (by linarith)

end Ostmann

end OAI
