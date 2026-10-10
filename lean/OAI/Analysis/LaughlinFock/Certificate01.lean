import Mathlib
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.LDL

namespace OAI

/-! Certificate01. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourZData_1 : Matrix (CopyLabel 1) (CopyLabel 1) ℚ :=
  copyMatrixData 1 [
    [0]
  ]

def fourLData_1 : Matrix (CopyLabel 1) (CopyLabel 1) ℚ :=
  copyMatrixData 1 [
    [1]
  ]

def fourPivotData_1 : CopyLabel 1 → ℚ :=
  copyDiagonalData 1 [0]

theorem fourOccupations_1 : highestFourOccupations 1 = ∅ := by
  decide +kernel

def fourHighestCache_1 : List (Occupation 24 × List ℚ) := [

]

theorem fourHighestChecked_1 : ∀ r : CopyLabel 1, ∀ A∈highestFourOccupations 1,
    kernelHighestEntry 1 r A = highestLookup fourHighestCache_1 r.val.val A := by
  rw [fourOccupations_1]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_1 (r s : CopyLabel 1) :
    integerFourGram 1 r s = fourZData_1 r s := by
  rw [integerFourGram_cached 1 fourHighestCache_1 fourHighestChecked_1]
  have h : ∀ r s : CopyLabel 1, cachedFourGram 1 fourHighestCache_1 r s = fourZData_1 r s := by
    simp only [cachedFourGram, fourOccupations_1]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_1 :
    ((integerCompression 1).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 1 = 0 := by
    rw [show integerFourGram 1 = fourZData_1 from Matrix.ext fourZChecked_1]
    have h : ∀ r s : CopyLabel 1, fourZData_1 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
