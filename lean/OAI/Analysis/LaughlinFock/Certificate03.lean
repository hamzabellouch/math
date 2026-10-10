import Mathlib
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.LDL

namespace OAI

/-! Certificate03. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourZData_3 : Matrix (CopyLabel 3) (CopyLabel 3) ℚ :=
  copyMatrixData 3 [
    [0, 0],
    [0, 0]
  ]

def fourLData_3 : Matrix (CopyLabel 3) (CopyLabel 3) ℚ :=
  copyMatrixData 3 [
    [1, 0],
    [0, 1]
  ]

def fourPivotData_3 : CopyLabel 3 → ℚ :=
  copyDiagonalData 3 [0, 0]

theorem fourOccupations_3 : highestFourOccupations 3 = ∅ := by
  decide +kernel

def fourHighestCache_3 : List (Occupation 24 × List ℚ) := [

]

theorem fourHighestChecked_3 : ∀ r : CopyLabel 3, ∀ A∈highestFourOccupations 3,
    kernelHighestEntry 3 r A = highestLookup fourHighestCache_3 r.val.val A := by
  rw [fourOccupations_3]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_3 (r s : CopyLabel 3) :
    integerFourGram 3 r s = fourZData_3 r s := by
  rw [integerFourGram_cached 3 fourHighestCache_3 fourHighestChecked_3]
  have h : ∀ r s : CopyLabel 3, cachedFourGram 3 fourHighestCache_3 r s = fourZData_3 r s := by
    simp only [cachedFourGram, fourOccupations_3]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_3 :
    ((integerCompression 3).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 3 = 0 := by
    rw [show integerFourGram 3 = fourZData_3 from Matrix.ext fourZChecked_3]
    have h : ∀ r s : CopyLabel 3, fourZData_3 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
