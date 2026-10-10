import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductPrescribedCutoff
import OAI.NumberTheory.Ostmann.Construction.SelectedCellGap

namespace OAI

/-! # Actual cell rounding in the recursive product and frequency budgets -/
namespace Ostmann

private theorem productExponent_rounding_le (T U : ℕ → ℝ) (W Z C R : ℝ) (n : ℕ)
    (hW : W ≤ Z + C) (hTU : ∀ j < n, U j - (2 : ℝ) ^ j * R ≤ T j) :
    movingProductExponent T W n ≤ movingProductExponent U Z n +
      (2 : ℝ) ^ n * (C + n * R) := by
  induction n with
  | zero => simpa only [movingProductExponent, pow_zero, Nat.cast_zero, mul_zero,
      zero_mul, add_zero, one_mul] using hW
  | succ n ih =>
    have hh := hTU n (Nat.lt_succ_self n)
    have hprev := ih (fun j hj => hTU j (Nat.lt_trans hj (Nat.lt_succ_self n)))
    rw [movingProductExponent, movingProductExponent, pow_succ, Nat.cast_add, Nat.cast_one]
    nlinarith only [hprev, hh]

theorem movingProductExponent_rounding_abs (T U : ℕ → ℝ) (W Z C R : ℝ) (n : ℕ)
    (hW : |W - Z| ≤ C) (hTU : ∀ j < n, |T j - U j| ≤ (2 : ℝ) ^ j * R) :
    |movingProductExponent T W n - movingProductExponent U Z n| ≤
      (2 : ℝ) ^ n * (C + n * R) := by
  obtain ⟨hWlo, hWhi⟩ := abs_le.mp hW
  have hu := productExponent_rounding_le T U W Z C R n (by linarith)
    (fun j hj => by have hh := (abs_le.mp (hTU j hj)).1; linarith)
  have hl := productExponent_rounding_le U T Z W C R n (by linarith)
    (fun j hj => by have hh := (abs_le.mp (hTU j hj)).2; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem movingProductFrequency_rounding_abs (T U : ℕ → ℝ) (W Z Y m C R : ℝ) (n : ℕ)
    (hW : |W - Z| ≤ C) (hTU : ∀ j < n, |T j - U j| ≤ (2 : ℝ) ^ j * R) :
    |movingProductFrequencyExponent T W Y m n - movingProductFrequencyExponent U Z Y m n| ≤
      (2 : ℝ) ^ n * (C + n * R) := by
  convert movingProductExponent_rounding_abs T U W Z C R n hW hTU using 1
  congr 1
  unfold movingProductFrequencyExponent
  ring

/-- The selected integer center is close to its target in the exact pivot
exponent used by the product cap, including the lower-edge loss. -/
theorem SelectedSmallTailCell.pivot_exponent_error
    {A B : Set ℕ} {N hi j : ℕ} {a C L X w : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L X hi D (w / 4) j) (G : ℝ) (n : ℕ) :
    |(G - 1 + ((2 ^ n * 4 : ℕ) : ℝ) * ((j : ℝ) - 1)) -
      (G + (2 : ℝ) ^ n * w)| ≤
        (2 : ℝ) ^ n * (256 * tailDefectBudget a C X + 9) := by
  have hlo := h.1
  have hhi := h.2.1
  have hD : 0 ≤ 64 * tailDefectBudget a C X + 1 := by linarith
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr0 : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hlow := mul_le_mul_of_nonneg_left hlo hr0
  have hupp := mul_le_mul_of_nonneg_left hhi hr0
  have hbudget := mul_le_mul_of_nonneg_left hD hr0
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact abs_le.mpr ⟨by nlinarith only [hlow, hbudget, hr], by nlinarith only [hupp, hr]⟩

/-- Rounding that fits the existing one-unit reserve preserves the already
proved uniform frequency-rate bound. -/
theorem movingProductFrequency_prescribed_rate (G J Y Bs BD Bz L : ℝ) (k n : ℕ)
    (hn : n ≤ k) (T : ℕ → ℝ) (W C R : ℝ)
    (hbase : 2 * G + J + (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - Y =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L))
    (hW : |W - (2 * G + J + (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum)| ≤ C)
    (hT : ∀ j < n, |T j - movingTargetPivotExponent G
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) j| ≤ (2 : ℝ) ^ j * R)
    (hbudget : C + n * R ≤ (spectatorBulkCount k L : ℝ))
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hk : 1 ≤ (k : ℝ) ^ 4)
    (hm : 4 ≤ (spectatorBulkCount k L : ℝ)) :
    movingProductFrequencyExponent T W Y (spectatorBulkCount k L) n ≤
      movingFrequencyRate Bs BD Bz ((k : ℝ) ^ 4) n * spectatorBulkCount k L := by
  have hh := movingProductFrequency_rounding_abs T
    (movingTargetPivotExponent G (movingCompensationTargets J (movingCompensationGaps k BD Bz L)))
    W _ Y (spectatorBulkCount k L) C R n hW hT
  rw [movingProductFrequency_prescribed G J Y Bs BD Bz L k n hn hbase] at hh
  have hb := movingCutoffExponent_bound Bs BD Bz ((k : ℝ) ^ 4)
    (spectatorBulkCount k L) n hBs hBD hBz hk hm
  have he := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ (2 : ℝ) ^ n)
  have hu := (abs_le.mp hh).2
  nlinarith only [hb, he, hu]

/-- The actual initial-cell error and every subsequent pivot-cell error
fit the existing one-unit frequency allowance at polynomial bulk scale. -/
theorem moving_cell_frequency_rounding_budget (k n : ℕ) (R D L : ℝ)
    (hk : 2 ≤ k) (hn : n ≤ k) (hD : 0 ≤ D)
    (hL : 1 ≤ L) (hDL : D ≤ R * L)
    (hlarge : 2 * (704 * R + 26) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L) :
    (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) +
      n * (256 * D + 9) ≤ (spectatorBulkCount k L : ℝ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hnk : (n : ℝ) ≤ k := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hnterm := mul_le_mul_of_nonneg_right hnk (show 0 ≤ 256 * D + 9 by positivity)
  have herror : (6 + 4 * k) * (64 * D + 1) + 2 * ((3 + 2 * k : ℕ) + 3) +
      n * (256 * D + 9) ≤ (k : ℝ) * (704 * R + 26) * L := by
    push_cast
    have hkd : 0 ≤ ((k : ℝ) - 2) * D := mul_nonneg (by linarith) hD
    have hdl := mul_le_mul_of_nonneg_left hDL (show 0 ≤ 704 * (k : ℝ) by positivity)
    have hconst := mul_le_mul_of_nonneg_left hL (show 0 ≤ 26 * (k : ℝ) by positivity)
    nlinarith only [hnterm, hkd, hdl, hconst, hk2]
  apply herror.trans
  calc
    _ ≤ (k : ℝ) ^ 4 / 2 * L := by
      have hh := mul_le_mul_of_nonneg_left hlarge hk0
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      nlinarith only [hh]
    _ = (k : ℝ) ^ 4 * L / 2 := by ring
    _ ≤ _ := spectatorBulkCount_half k L hscale

end Ostmann

end OAI
