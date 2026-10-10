import OAI.Combinatorics.EditApproximation.Coarse.CoarseRootWork
import OAI.Combinatorics.EditApproximation.Geometry.HeightPowerWork

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem bitPowerBitBudget_mono (d e A C : ℕ) (hd : d ≤ e) (hA : A ≤ C) :
    bitPowerBitBudget d A ≤ bitPowerBitBudget e C := by
  have hw : (d + 1) * (A + 1) + 1 ≤ (e + 1) * (C + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  have hp := Nat.pow_le_pow_left hw 2
  have hc := Nat.mul_le_mul hd (Nat.mul_le_mul_left 200 hp)
  simpa only [bitPowerBitBudget] using Nat.add_le_add_left hc 1

def coarseNumericalUnit (H : ℕ) : ℕ :=
  bitPowerBitBudget H (7 * H ^ 3 + 3) +
    1000 * (10 * (H + 2) * (H ^ 3 + 1) + 1) ^ 2 +
    100001000 * (H ^ 3 + 1) ^ 2

 theorem coarseNumericalUnit_polynomial (H : ℕ) :
    coarseNumericalUnit H ≤ 10000000000 * (H + 1) ^ 10 := by
  have hp (j : ℕ) (hj : j ≤ 10) : H ^ j ≤ (H + 1) ^ 10 :=
    (Nat.pow_le_pow_left (Nat.le_succ H) j).trans
      (Nat.pow_le_pow_right (by omega) hj)
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h6 := hp 6 (by decide)
  have h7 := hp 7 (by decide)
  have h8 := hp 8 (by decide)
  have h9 := hp 9 (by decide)
  unfold coarseNumericalUnit bitPowerBitBudget
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

 theorem coarseNumericalUnit_le_power (H : ℕ) (hH : 10 ≤ H) :
    coarseNumericalUnit H ≤ H ^ 30 := by
  have hc : 10000000000 ≤ H ^ 10 := by
    have h := Nat.pow_le_pow_left hH 10
    norm_num at h ⊢
    exact h
  have hh : H + 1 ≤ H ^ 2 := by nlinarith
  have hp := Nat.pow_le_pow_left hh 10
  calc
    coarseNumericalUnit H ≤ 10000000000 * (H + 1) ^ 10 := coarseNumericalUnit_polynomial H
    _ ≤ H ^ 10 * (H ^ 2) ^ 10 := Nat.mul_le_mul hc hp
    _ = H ^ 30 := by rw [← pow_mul, ← pow_add]

 theorem coarseRootWithWork_height_bound {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N D H : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1))
    (hBbits : Nat.size B + 2 ≤ H ^ 3) (hqbits : Nat.size q + 2 ≤ H ^ 3)
    (hLbits : Nat.size L + 2 ≤ H ^ 3) (hNbits : Nat.size N + 2 ≤ H ^ 3)
    (hd : Nat.size (coarseCommonDenominator 1 q L B d) ≤ D) (hD : D ≤ H ^ 3)
    (hdepth : d ≤ H)
    (hbound : Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * D + 1 ≤ H ^ 3)
    (hstart : start + tree.word.length ≤ N) :
    (coarseRootWithWork k q L hB hq hL frame tree draws start shift).2 ≤
      coarseNumericalUnit H * (2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1) := by
  have h := coarseRootWithWork_cost k q L N D (H ^ 3) hB hq hL frame tree draws start shift
    hBbits hqbits hLbits hNbits hd hD hbound hstart
  have hp := bitPowerBitBudget_mono d H (7 * H ^ 3 + 3) (7 * H ^ 3 + 3) hdepth le_rfl
  have hm : 10 * (d + 2) * (H ^ 3 + 1) + 1 ≤ 10 * (H + 2) * (H ^ 3 + 1) + 1 := by
    nlinarith only [Nat.mul_le_mul_right (10 * (H ^ 3 + 1)) hdepth]
  have hc := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left hm 2)
  have hf := Nat.mul_le_mul_left
    (bitPowerBitBudget H (7 * H ^ 3 + 3) + 1000 * (10 * (H + 2) * (H ^ 3 + 1) + 1) ^ 2)
    (show 1 ≤ 2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1 by omega)
  unfold coarseNumericalUnit
  nlinarith only [h, hp, hc, hf]

end BinaryFraction
end EditApproximation

end OAI
