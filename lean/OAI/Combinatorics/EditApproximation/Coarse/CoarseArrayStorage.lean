import OAI.Combinatorics.EditApproximation.Coarse.CoarseRootBounds
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedInitial

namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- The stored numerator bits, denominator bits, sign and list links. -/
def coarseArrayStorage : CoarseBinaryArray → ℕ
  | none => 1
  | some cells => 1 + (cells.map fun a => a.numerator.bits.length + a.denominator.length + 3).sum

theorem coarseArrayStorage_le (two : BinaryFraction) (n V D A : ℕ)
    (array : CoarseBinaryArray) (h : CoarseBinaryBox two n V D A array) :
    coarseArrayStorage array ≤ 1 + n * (2 * A + 3) := by
  cases array with
  | none => simp only [coarseArrayStorage]; omega
  | some cells =>
    have hw (a : BinaryFraction) (ha : a ∈ cells) :
        a.numerator.bits.length + a.denominator.length + 3 ≤ 2 * A + 3 := by
      have hab := ((h cells rfl).2 a ha).2.2.2.2
      unfold width at hab
      omega
    have hsum (values : List BinaryFraction)
        (hv : ∀ a ∈ values, a.numerator.bits.length + a.denominator.length + 3 ≤ 2 * A + 3) :
        (values.map fun a => a.numerator.bits.length + a.denominator.length + 3).sum ≤
          values.length * (2 * A + 3) := by
      induction values with
      | nil => simp
      | cons a values ih =>
        have ha := hv a List.mem_cons_self
        have ht := ih (fun b hb => hv b (List.mem_cons_of_mem _ hb))
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
    have hs := hsum cells hw
    rw [(h cells rfl).1] at hs
    exact Nat.add_le_add_left hs 1

/-- The actual array immediately before the root lookup. -/
def coarseRootArray {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) : CoarseBinaryArray :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  (coarseBinaryEval k q L frame two tree draws allowance start).1

theorem coarseRootArray_storage {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L N D A : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ)
    (hBbits : Nat.size B + 2 ≤ A) (hqbits : Nat.size q + 2 ≤ A)
    (hLbits : Nat.size L + 2 ≤ A) (hNbits : Nat.size N + 2 ≤ A)
    (hd : Nat.size (coarseCommonDenominator 1 q L B d) ≤ D)
    (hbound : Nat.size (coarseLevelMagnitude N k B d + 2) + 2 * D + 1 ≤ A)
    (hstart : start + tree.word.length ≤ N) :
    coarseArrayStorage (coarseRootArray k q L hB hq hL frame tree draws start) ≤
      1 + (2 * k + 1) * (2 * A + 3) := by
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
  have hc := (coarseBinaryEval_bitWork k q L N d D A frame two tree draws hB hq hL htwo
    htwocell.2.2.2.2 (by rw [htwoDen]; exact hd) htwoDen hBbits hqbits hLbits hNbits hbound
    0 (by omega) allowance start hacell hpath hstart).1
  exact coarseArrayStorage_le two _ _ D A _ hc

def coarseIndexedRootArray {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) : CoarseBinaryArray :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  (coarseIndexedWithWork k q L (coarseEntryWidth x y) x y two d 0 draws allowance 0).1

theorem coarseIndexedRootArray_eq {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    coarseIndexedRootArray k q L hB hq hL x y draws =
      coarseRootArray k q L hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 := by
  unfold coarseIndexedRootArray coarseRootArray
  dsimp only
  rw [coarseIndexedWithWork_value, coarseReadCore_eq k q L (coarseEntryWidth x y) x y
    (le_max_left _ _) (le_max_right _ _)]
  simp only [Nat.zero_add, coarseReadTree_entry]

end BinaryFraction
end EditApproximation

end OAI
