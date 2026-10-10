import OAI.Combinatorics.EditApproximation.Coarse.CoarseRootExecution
import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryBitWork
import OAI.Combinatorics.EditApproximation.Coarse.CoarseWeightSimulation

namespace OAI

namespace EditApproximation
namespace BinaryFraction

 theorem coarseRootWithWork_cost {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N D A : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1))
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hd : Nat.size (coarseCommonDenominator 1 q L B d) ≤ D) (hD : D ≤ A)
    (hbound : Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * D + 1 ≤ A)
    (hstart : start + tree.word.length ≤ N) :
    (coarseRootWithWork k q L hB hq hL frame tree draws start shift).2 ≤
      bitPowerBitBudget d (7 * A + 3) + 1000 * (10 * (d + 2) * (A + 1) + 1) ^ 2 +
      100001000 * (A + 1) ^ 2 * (2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1) := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  have hden := coarseRootDenominator_value B q L d
  have hdenLen : den.1.length ≤ D := (coarseRootDenominator_length B q L d).trans_le hd
  have htwo : two.value = 2 := coarseGridNatWithWork_value _ _ 2
  have htwoDen : two.representation.den = coarseCommonDenominator 1 q L B d :=
    (coarseGridNatWithWork_den _ _ 2).trans hden
  have hkwidth : Nat.size k + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      ((coarseLevelMagnitude_ge N k B d).trans (by omega))) _) _).trans hbound
  have h2width : Nat.size 2 + 2 * D + 1 ≤ A :=
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size (by omega : 2 ≤ coarseLevelMagnitude N k B d + 2)) _) _).trans hbound
  have htwocell : CoarseGridCell two two 2 D A :=
    coarseGridNatWithWork_bounds two den.1 denPos 2 2 D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl h2width
  have hacell : CoarseGridCell two allowance k D A :=
    coarseGridNatWithWork_bounds two den.1 denPos k k D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl hkwidth
  have hav : allowance.value = k := coarseGridNatWithWork_value _ _ k
  have hpath : allowance.value.den ∣ (L * B * q) ^ 0 := by
    simp only [hav, Rat.den_natCast, one_dvd]
  have hc := (coarseBinaryEval_bitWork k q L N d D A frame two tree draws hB hq hL htwo
    htwocell.2.2.2.2 (by rw [htwoDen]; exact hd) htwoDen hBbits hqbits hLbits hNbits hbound
    0 (by omega) allowance start hacell hpath hstart).2
  have hw := coarseBinaryWeight_le k q L d tree draws hB hq hL 0 (by omega) allowance
    (hacell.1.trans htwoDen) hpath
  rw [hav] at hw
  have heval := hc.trans (Nat.mul_le_mul_left (100000000 * (A + 1) ^ 2) hw)
  have htwoCost := coarseGridNatWithWork_cost den.1 denPos 2 A (by omega)
    (hdenLen.trans hD)
  have haCost := coarseGridNatWithWork_cost den.1 denPos k A (by omega) (hdenLen.trans hD)
  have hdenCost := coarseDenominatorWithWork_cost (1 : ℕ).bits q.bits L.bits B.bits d A
    (by simp only [Nat.size_eq_bits_len, Nat.size_one]; omega)
    (by rw [Nat.size_eq_bits_len]; omega)
    (by rw [Nat.size_eq_bits_len]; omega)
    (by rw [Nat.size_eq_bits_len]; omega)
  change den.2 ≤ _ at hdenCost
  have hfactor := Nat.mul_le_mul_left ((A + 1) ^ 2)
    (show 1 ≤ 2 * coarseActiveArrayWork k q (1 / L) tree draws k + 1 by omega)
  change den.2 + (coarseGridNatWithWork den.1 denPos 2).2 +
    (coarseGridNatWithWork den.1 denPos k).2 +
    (coarseBinaryEval k q L frame two tree draws allowance start).2 + 1 ≤ _
  nlinarith only [heval, htwoCost, haCost, hdenCost, hfactor, Nat.zero_le A,
    Nat.zero_le (coarseActiveArrayWork k q (1 / L) tree draws k)]

end BinaryFraction
end EditApproximation

end OAI
