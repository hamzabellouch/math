import OAI.Combinatorics.EditApproximation.Binary.BinaryCellGrid
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal eligibility scans for the whole-cell representative list. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem centerEligibilityWithWork_value (b F : ℕ) (a initial : BinaryFraction) :
    (centerEligibilityWithWork b F a initial).1 = true ↔
      (b : ℚ) / (4 * a.value) ≤ initial.value ∧ initial.value ≤ 8 * F * b := by
  simp only [centerEligibilityWithWork, Bool.and_eq_true, leWithWork_value,
    divWithWork_value, canonicalMulWithWork_value, nat_value]
  norm_num

def cellCentersWithWork {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ) :
    List (TargetInterval n) × ℕ :=
  let spacing := seedGridSpacingWithWork b P
  let side := canonicalMulWithWork theta (nat b)
  let states := cellStatesWithWork n (bitWordValue spacing.1) side.1 cell
  let selected := filterWithWork (fun r => centerEligibilityWithWork b F a (initial r)) states.1
  (selected.1, spacing.2 + side.2 + states.2 + selected.2 + 3)

@[simp] theorem cellCentersWithWork_value {n : ℕ} (P F b : ℕ) (a theta : BinaryFraction)
    (initial : TargetInterval n → BinaryFraction) (cell : ℕ × ℕ) (hP : 0 < P) :
    (cellCentersWithWork P F b a theta initial cell).1 =
      cellRepresentativeStates n P F b a.value (fun r => (initial r).value) theta.value cell := by
  have htest (r : TargetInterval n) : (centerEligibilityWithWork b F a (initial r)).1 =
      decide ((b : ℚ) / (4 * a.value) ≤ (initial r).value ∧ (initial r).value ≤ 8 * F * b) :=
    Bool.eq_iff_iff.mpr (by simp only [centerEligibilityWithWork_value, decide_eq_true_eq])
  simp only [cellCentersWithWork, filterWithWork_value, cellStatesWithWork_value,
    seedGridSpacingWithWork_value b P hP, canonicalMulWithWork_value, nat_value,
    htest, cellRepresentativeStates]

end BinaryFraction
end EditApproximation

end OAI
