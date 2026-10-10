import OAI.NumberTheory.Ostmann.Arithmetic.MovingFinalGap
import OAI.NumberTheory.Ostmann.Construction.RoundedEnergyCutoffs

namespace OAI

/-! # The actual accumulated gaps and rounded frequency cutoffs of Section 7 -/

namespace Ostmann
open scoped BigOperators

/-- The square-root reserve agrees with the proved bottom cutoff at `4m`. -/
noncomputable def movingCutoffExponent (Bs BD Bz z m : ℝ) (n : ℕ) : ℝ :=
  spectatorBaseGap Bs z m +
    ∑ j ∈ Finset.range n, spectatorStepGap BD Bz z ((2 : ℝ) ^ j) m +
      (2 : ℝ) ^ n * Real.sqrt (4 * m)

noncomputable def movingNaturalCutoff (Bs BD Bz z m : ℝ) (n : ℕ) : ℕ :=
  ⌊Real.exp (movingCutoffExponent Bs BD Bz z m n)⌋₊

/-- One unit of reserve is left for the root-frequency count. -/
noncomputable def movingFrequencyRate (Bs BD Bz z : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * (Bs + 8 * Real.log z + BD + Bz * Real.log z +
    (2 / 5 : ℝ) * Real.log ((2 : ℝ) ^ n) + 2)

theorem movingCutoffExponent_zero (Bs BD Bz z m : ℝ) :
    movingCutoffExponent Bs BD Bz z m 0 = spectatorBaseGap Bs z m + Real.sqrt (4 * m) := by
  simp [movingCutoffExponent]

theorem movingCutoffExponent_succ (Bs BD Bz z m : ℝ) (n : ℕ) :
    movingCutoffExponent Bs BD Bz z m (n + 1) =
      movingCutoffExponent Bs BD Bz z m n +
      spectatorStepGap BD Bz z ((2 : ℝ) ^ n) m + (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  simp only [movingCutoffExponent, Finset.sum_range_succ, pow_succ]
  ring

private theorem moving_sum_two_pow (n : ℕ) :
    (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) + 1 = (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

theorem movingCutoffExponent_bound (Bs BD Bz z m : ℝ) (n : ℕ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (hm : 4 ≤ m) :
    movingCutoffExponent Bs BD Bz z m n ≤
      (movingFrequencyRate Bs BD Bz z n - (2 : ℝ) ^ n) * m := by
  let Q := BD + Bz * Real.log z + (2 / 5 : ℝ) * Real.log ((2 : ℝ) ^ n)
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg hz
  have hlogr : 0 ≤ Real.log ((2 : ℝ) ^ n) := Real.log_nonneg hr
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hm0 : 0 ≤ m := by linarith
  have hsum : (∑ j ∈ Finset.range n, spectatorStepGap BD Bz z ((2 : ℝ) ^ j) m) ≤
      (2 : ℝ) ^ n * Q * m := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, (2 : ℝ) ^ j * Q * m := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := (Finset.mem_range.mp hj).le
        have hp : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hjn
        have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ j) hp
        have hc : BD + Bz * Real.log z + (2 / 5 : ℝ) * Real.log ((2 : ℝ) ^ j) ≤ Q := by
          dsimp only [Q]
          linarith
        unfold spectatorStepGap
        nlinarith only [mul_le_mul_of_nonneg_left hc (mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j) hm0)]
      _ = (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) * Q * m := by
        rw [Finset.sum_mul, Finset.sum_mul]
      _ ≤ (2 : ℝ) ^ n * Q * m := by
        have hh := moving_sum_two_pow n
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith : (∑ j ∈ Finset.range n, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ n) hQ) hm0
  have hsqrt : Real.sqrt (4 * m) ≤ m := by
    have hs := Real.sq_sqrt (show 0 ≤ 4 * m by positivity)
    have hp : 0 ≤ m * (m - 4) := mul_nonneg hm0 (by linarith)
    nlinarith [Real.sqrt_nonneg (4 * m)]
  have hbase : Bs + 8 * Real.log z ≤ (2 : ℝ) ^ n * (Bs + 8 * Real.log z) := by
    exact le_mul_of_one_le_left (by positivity) hr
  have hr0 : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hb := mul_le_mul_of_nonneg_right hbase hm0
  have hs := mul_le_mul_of_nonneg_left hsqrt hr0
  unfold movingCutoffExponent spectatorBaseGap movingFrequencyRate
  dsimp only [Q] at hsum
  nlinarith only [hsum, hb, hs]

theorem movingNaturalCutoff_frequency_bound (Bs BD Bz z m : ℝ) (n : ℕ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (hm : 4 ≤ m) :
    (movingNaturalCutoff Bs BD Bz z m n : ℝ) ≤ Real.exp (movingFrequencyRate Bs BD Bz z n * m) ∧
    ((transferFrequencyRange (movingNaturalCutoff Bs BD Bz z m n)).card : ℝ) ≤
      Real.exp (movingFrequencyRate Bs BD Bz z n * m) := by
  let E := movingCutoffExponent Bs BD Bz z m n
  let A := movingFrequencyRate Bs BD Bz z n
  have hE := movingCutoffExponent_bound Bs BD Bz z m n hBs hBD hBz hz hm
  have hfloor : (movingNaturalCutoff Bs BD Bz z m n : ℝ) ≤ Real.exp E :=
    Nat.floor_le (Real.exp_pos _).le
  have hE0 : 0 ≤ E := by
    dsimp only [E, movingCutoffExponent, spectatorBaseGap]
    have hlogz := Real.log_nonneg hz
    apply add_nonneg
    · apply add_nonneg (mul_nonneg (by positivity) (by linarith))
      apply Finset.sum_nonneg
      intro j _
      have hl := Real.log_nonneg (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ j)
      unfold spectatorStepGap
      positivity
    · positivity
  have hmargin : Real.log 3 ≤ (2 : ℝ) ^ n * m := by
    have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    nlinarith
  have hcard : ((transferFrequencyRange (movingNaturalCutoff Bs BD Bz z m n)).card : ℝ) ≤
      3 * Real.exp E := by
    rw [card_transferFrequencyRange]
    push_cast
    have he1 := Real.one_le_exp hE0
    linarith
  have hfinal : 3 * Real.exp E ≤ Real.exp (A * m) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [A, E]
    nlinarith only [hE, hmargin]
  exact ⟨hfloor.trans ((by nlinarith [Real.exp_pos E] : Real.exp E ≤ 3 * Real.exp E).trans hfinal),
    hcard.trans hfinal⟩

end Ostmann

end OAI
