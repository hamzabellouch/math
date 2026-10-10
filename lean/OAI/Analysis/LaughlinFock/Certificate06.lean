import Mathlib
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.LDL

namespace OAI

/-! Certificate06. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourZData_6 : Matrix (CopyLabel 6) (CopyLabel 6) ℚ :=
  copyMatrixData 6 [
    [0, 0, 0],
    [0, 0, 0],
    [0, 0, 0]
  ]

def fourLData_6 : Matrix (CopyLabel 6) (CopyLabel 6) ℚ :=
  copyMatrixData 6 [
    [1, 0, 0],
    [0, 1, 0],
    [0, 0, 1]
  ]

def fourPivotData_6 : CopyLabel 6 → ℚ :=
  copyDiagonalData 6 [0, 0, 0]

theorem fourOccupations_6 : highestFourOccupations 6 = {{0,1,2,4}} := by
  decide +kernel

def fourHighestCache_6 : List (Occupation 24 × List ℚ) := [
  ({0,1,2,4}, [0, 0, 0])
]

theorem fourHighestChecked_6 : ∀ r : CopyLabel 6, ∀ A∈highestFourOccupations 6,
    kernelHighestEntry 6 r A = highestLookup fourHighestCache_6 r.val.val A := by
  rw [fourOccupations_6]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_6 (r s : CopyLabel 6) :
    integerFourGram 6 r s = fourZData_6 r s := by
  rw [integerFourGram_cached 6 fourHighestCache_6 fourHighestChecked_6]
  have h : ∀ r s : CopyLabel 6, cachedFourGram 6 fourHighestCache_6 r s = fourZData_6 r s := by
    simp only [cachedFourGram, fourOccupations_6]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_6 :
    ((integerCompression 6).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 6 = 0 := by
    rw [show integerFourGram 6 = fourZData_6 from Matrix.ext fourZChecked_6]
    have h : ∀ r s : CopyLabel 6, fourZData_6 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
