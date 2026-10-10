import Mathlib
import OAI.Analysis.LaughlinFock.GramCache
import OAI.Analysis.LaughlinFock.LDL

namespace OAI

/-! Certificate02. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

def fourZData_2 : Matrix (CopyLabel 2) (CopyLabel 2) ℚ :=
  copyMatrixData 2 [
    [0]
  ]

def fourLData_2 : Matrix (CopyLabel 2) (CopyLabel 2) ℚ :=
  copyMatrixData 2 [
    [1]
  ]

def fourPivotData_2 : CopyLabel 2 → ℚ :=
  copyDiagonalData 2 [0]

theorem fourOccupations_2 : highestFourOccupations 2 = ∅ := by
  decide +kernel

def fourHighestCache_2 : List (Occupation 24 × List ℚ) := [

]

theorem fourHighestChecked_2 : ∀ r : CopyLabel 2, ∀ A∈highestFourOccupations 2,
    kernelHighestEntry 2 r A = highestLookup fourHighestCache_2 r.val.val A := by
  rw [fourOccupations_2]
  apply @of_decide_eq_true _ (boundedMatrixEntriesDecidable _ _ _)
  decide +kernel

theorem fourZChecked_2 (r s : CopyLabel 2) :
    integerFourGram 2 r s = fourZData_2 r s := by
  rw [integerFourGram_cached 2 fourHighestCache_2 fourHighestChecked_2]
  have h : ∀ r s : CopyLabel 2, cachedFourGram 2 fourHighestCache_2 r s = fourZData_2 r s := by
    simp only [cachedFourGram, fourOccupations_2]
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  exact h r s

theorem integer_certificate_2 :
    ((integerCompression 2).map (algebraMap ℚ ℂ)).PosSemidef := by
  have he : integerFourGram 2 = 0 := by
    rw [show integerFourGram 2 = fourZData_2 from Matrix.ext fourZChecked_2]
    have h : ∀ r s : CopyLabel 2, fourZData_2 r s = (0:ℚ) := by
      apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
      decide +kernel
    exact Matrix.ext h
  simp only [integerCompression, he, Matrix.zero_mul, Matrix.map_zero _ (map_zero _)]
  exact Matrix.PosSemidef.zero

end LaughlinFock
end

end OAI
