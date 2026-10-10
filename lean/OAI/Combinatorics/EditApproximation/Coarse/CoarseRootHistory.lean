import OAI.Combinatorics.EditApproximation.Coarse.CoarseHistoryBound
import OAI.Combinatorics.EditApproximation.Coarse.CoarseCompleteWork

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseRootArrayHistory {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) : ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  coarseBinaryArrayHistory k q L frame two tree draws allowance start

theorem coarseRootArrayHistory_bound {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N D A : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ)
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hd : Nat.size (coarseCommonDenominator 1 q L B d) ≤ D)
    (hbound : Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * D + 1 ≤ A)
    (hstart : start + tree.word.length ≤ N) :
    coarseRootArrayHistory k q L hB hq hL frame tree draws start ≤
      (32 * (A + 1)) * ((B * (2 * k + 1) + 1) * coarseCompleteNodes B d) := by
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
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.size_le_size
      (by omega : 2 ≤ coarseLevelMagnitude N k B d + 2)) _) _).trans hbound
  have htwocell : CoarseGridCell two two 2 D A :=
    coarseGridNatWithWork_bounds two den.1 denPos 2 2 D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl h2width
  have hacell : CoarseGridCell two allowance k D A :=
    coarseGridNatWithWork_bounds two den.1 denPos k k D A
      (coarseGridNatWithWork_den _ _ 2).symm hdenLen le_rfl hkwidth
  have hav : allowance.value = k := coarseGridNatWithWork_value _ _ k
  have hpath : allowance.value.den ∣ (L * B * q) ^ 0 := by
    simp only [hav, Rat.den_natCast, one_dvd]
  have hh := coarseBinaryArrayHistory_bound k q L N d D A frame two tree draws hB hq hL htwo
    htwocell.2.2.2.2 (by rw [htwoDen]; exact hd) htwoDen hBbits hqbits hLbits hNbits hbound
    0 (by omega) allowance start hacell hpath hstart
  exact hh.trans (Nat.mul_le_mul_left _ (coarseBinaryWeight_le_complete k q L tree draws allowance))

end BinaryFraction
end EditApproximation

end OAI
