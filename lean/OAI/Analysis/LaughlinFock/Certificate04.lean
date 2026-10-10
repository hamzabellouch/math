import Mathlib
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.LDL

namespace OAI

/-! Certificate04. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourZData_4 : Matrix (CopyLabel 4) (CopyLabel 4) ℚ :=
  copyMatrixData 4 [
    [0, 0],
    [0, 0]
  ]

def fourLData_4 : Matrix (CopyLabel 4) (CopyLabel 4) ℚ :=
  copyMatrixData 4 [
    [1, 0],
    [0, 1]
  ]

def fourPivotData_4 : CopyLabel 4 → ℚ :=
  copyDiagonalData 4 [0, 0]

theorem fourOccupations_4 : highestFourOccupations 4 = ∅ := by
  decide +kernel

def fourHighestCache_4 : List (Occupation 24 × List ℚ) := [

]

theorem fourHighestChecked_4 : ∀ r : CopyLabel 4, ∀ A∈highestFourOccupations 4,
    kernelHighestEntry 4 r A = highestLookup fourHighestCache_4 r.val.val A := by
  rw [fourOccupations_4]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_4 (r s : CopyLabel 4) :
    integerFourGram 4 r s = fourZData_4 r s := by
  rw [integerFourGram_cached 4 fourHighestCache_4 fourHighestChecked_4]
  have h : ∀ r s : CopyLabel 4, cachedFourGram 4 fourHighestCache_4 r s = fourZData_4 r s := by
    simp only [cachedFourGram, fourOccupations_4]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_4 :
    ((integerCompression 4).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 4 = 0 := by
    rw [show integerFourGram 4 = fourZData_4 from Matrix.ext fourZChecked_4]
    have h : ∀ r s : CopyLabel 4, fourZData_4 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
