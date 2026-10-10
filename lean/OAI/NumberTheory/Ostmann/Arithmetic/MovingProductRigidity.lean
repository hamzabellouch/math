import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductRounding

namespace OAI

/-! # The integer rigidity margin survives the actual selected cell centers -/
namespace Ostmann

theorem movingProductFrequency_gap (T : ℕ → ℝ) (W Y m : ℝ) (n : ℕ) :
    (movingProductExponent T W n - 2 * T n) - movingProductFrequencyExponent T W Y m n =
      Y - 2 * T n - (2 : ℝ) ^ n * Real.sqrt (4 * m) := by
  unfold movingProductFrequencyExponent
  ring

/-- The initial center error cancels from this margin. Only the current
pivot-cell error remains, twice. -/
theorem movingProductFrequency_rigidity_margin (T U : ℕ → ℝ) (W Z Y m R : ℝ) (n : ℕ)
    (hT : T n ≤ U n + (2 : ℝ) ^ n * R) (hR : R ≤ m / 40)
    (hideal : (3 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent U Z n - 2 * U n) -
        movingProductFrequencyExponent U Z Y m n) :
    (1 / 10 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent T W n - 2 * T n) -
        movingProductFrequencyExponent T W Y m n := by
  rw [movingProductFrequency_gap] at hideal ⊢
  have he := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ (2 : ℝ) ^ n)
  nlinarith only [hideal, hT, he]

theorem movingProductFrequency_prescribed_margin (G J Y Bs BD Bz L : ℝ) (k n : ℕ)
    (hn : n < k) (T : ℕ → ℝ) (W R : ℝ)
    (hbase : 2 * G + J + (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - Y =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L))
    (hT : T n ≤ movingTargetPivotExponent G
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)) n + (2 : ℝ) ^ n * R)
    (hR : R ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz) (hk : 1 ≤ (k : ℝ) ^ 4)
    (hm : 64 ≤ (spectatorBulkCount k L : ℝ)) :
    (1 / 10 : ℝ) * (2 : ℝ) ^ n * spectatorBulkCount k L ≤
      (movingProductExponent T W n - 2 * T n) -
        movingProductFrequencyExponent T W Y (spectatorBulkCount k L) n := by
  let ds := movingCompensationGaps k BD Bz L
  let ws := movingCompensationTargets J ds
  let U := movingTargetPivotExponent G ws
  let Z := 2 * G + J + ws.sum
  apply movingProductFrequency_rigidity_margin T U W Z Y (spectatorBulkCount k L) R n hT hR
  have he := movingProductExponent_target_gap G J ds n (by simpa only [ds, movingCompensationGaps_length] using hn)
  have hfreq := movingProductFrequency_prescribed G J Y Bs BD Bz L k n hn.le hbase
  change movingProductFrequencyExponent U Z Y (spectatorBulkCount k L) n = _ at hfreq
  change movingProductExponent U Z n - 2 * U n = _ at he
  rw [hfreq, he]
  have hg : (2 : ℝ) ^ n * (ds.drop n).headD 0 =
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ n) (spectatorBulkCount k L) := by
    have hs := movingProductFrequency_prescribed G J Y Bs BD Bz L k (n + 1) (by omega) hbase
    have hr := movingProductFrequency_reserve U Z Y (spectatorBulkCount k L) n
    change movingProductFrequencyExponent U Z Y (spectatorBulkCount k L) (n + 1) = _ at hs
    rw [hs, hfreq, movingCutoffExponent_succ] at hr
    linarith only [hr, he]
  rw [hg]
  exact movingCutoff_diagonal_reserve Bs BD Bz ((k : ℝ) ^ 4) (spectatorBulkCount k L)
    hBD hBz hk hm n

theorem movingProductNaturalCutoff_rigidity (T : ℕ → ℝ) (W Y m C : ℝ)
    (n P R : ℕ)
    (hP : (P : ℝ) ≤ Real.exp (T n + C))
    (hR : Real.exp (movingProductExponent T W n - T n - C) ≤ (R : ℝ))
    (hmargin : Real.log 2 + 2 * C <
      (movingProductExponent T W n - 2 * T n) - movingProductFrequencyExponent T W Y m n) :
    2 * P * movingProductNaturalCutoff T W Y m n < R := by
  apply transfer_integer_rigidity_gap P (movingProductNaturalCutoff T W Y m n) R
    (T n) (movingProductExponent T W n - 2 * T n)
    (movingProductFrequencyExponent T W Y m n) C hP
    (Nat.floor_le (Real.exp_pos _).le) _ hmargin
  convert hR using 1
  congr 1
  ring

end Ostmann

end OAI
