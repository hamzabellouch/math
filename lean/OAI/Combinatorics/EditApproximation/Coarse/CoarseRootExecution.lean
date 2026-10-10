import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryCorrectness
import OAI.Combinatorics.EditApproximation.Coarse.CoarseBinaryRead
import OAI.Combinatorics.EditApproximation.Coarse.CoarseDenominatorArithmetic
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem coarseRootDenominator_value (B q L d : ℕ) :
    bitWordValue (coarseRootDenominator B q L d).1 = coarseCommonDenominator 1 q L B d := by
  simp only [coarseRootDenominator, coarseDenominatorWithWork_value, bitWordValue_bits]

 theorem coarseRootDenominator_length (B q L d : ℕ) :
    (coarseRootDenominator B q L d).1.length = Nat.size (coarseCommonDenominator 1 q L B d) := by
  simp only [coarseRootDenominator, coarseDenominatorWithWork_length, bitWordValue_bits]

 theorem coarseRootDenominator_pos (B q L d : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) :
    0 < bitWordValue (coarseRootDenominator B q L d).1 := by
  rw [coarseRootDenominator_value]
  unfold coarseCommonDenominator
  positivity

/-- Counted root setup and array lookup around the complete binary coarse
recursion. The common denominator is built from bits, not a free conversion. -/
def coarseRootWithWork {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1)) :
    BinaryFraction × ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  let evaluated := coarseBinaryEval k q L frame two.1 tree draws allowance.1 start
  (coarseBinaryRead evaluated.1 shift.val,
    den.2 + two.2 + allowance.2 + evaluated.2 + 1)

 theorem coarseRootWithWork_value {B d : ℕ} {α : Type*} [DecidableEq α]
    (k q L : ℕ) (hk : 0 < k) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (frame : List (Option α)) (tree : CoarseSourceTree B α d)
    (draws : CoarseThresholdDraws B d) (start : ℕ) (shift : Fin (2 * k + 1)) :
    (coarseRootWithWork k q L hB hq hL frame tree draws start shift).1.value =
      coarseThresholdEstimate k q (1 / L) frame tree draws k start shift := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  have ht : two.value = 2 := coarseGridNatWithWork_value _ _ 2
  have hd : two.representation.den = coarseCommonDenominator 1 q L B d :=
    (coarseGridNatWithWork_den _ _ 2).trans (coarseRootDenominator_value B q L d)
  have had : allowance.representation.den = two.representation.den := by
    rw [coarseGridNatWithWork_den, coarseGridNatWithWork_den]
  have hav : allowance.value = k := coarseGridNatWithWork_value _ _ k
  have hp : allowance.value.den ∣ (L * B * q) ^ 0 := by simp only [hav, Rat.den_natCast, one_dvd]
  have hr := coarseBinaryEval_rep k q L d frame two tree draws hB hq hL ht hd 0
    (by omega) allowance start had hp
  change (coarseBinaryRead (coarseBinaryEval k q L frame two tree draws allowance start).1 shift.val).value = _
  rw [coarseBinaryRead_rep _ _ hr, coarseArrayEval_read]
  · rw [hav]
  · exact_mod_cast hq
  · exact one_div_pos.mpr (by exact_mod_cast hL)
  · rw [hav]; exact_mod_cast hk

end BinaryFraction
end EditApproximation

end OAI
