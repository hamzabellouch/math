import Mathlib
import OAI.Analysis.LaughlinFock.SparseTrace

namespace OAI

/-! Parts Trace. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

def collectNumericRowParts (D : ℕ) (t : Fin 8) : List (List CollectedFourTerm) :=
  (numericRowData t).map fun b => (numericRowData t).flatMap fun c =>
    if D ≤ b.p+b.j+c.i then [collectFourTerm D t.val b c] else []

def collectedFourPartsTrace (D r s : ℕ) (ls : Fin 8 → List (List CollectedFourTerm)) : ℤ :=
  ∑ t : Fin 8, -(directIntegerSum (directIntegerSum (collectedTermValue D r s)) (ls t))

theorem collectNumericRowParts_sum (D : ℕ) (t : Fin 8) (r s : ℕ) :
    numericFourTrace D t r s =
      -(directIntegerSum (directIntegerSum (collectedTermValue D r s))
        (collectNumericRowParts D t)) := by
  rw [collectNumericRow_sum]
  simp only [collectNumericRow, collectNumericRowParts, List.map_flatMap,
    list_flatMap_sum_int, ← directIntegerSum_spec, List.map_map, Function.comp_def]

theorem integerRowsFourTrace_parts {D : ℕ} (hD : D ≤ 23)
    (ls : Fin 8 → List (List CollectedFourTerm))
    (hls : ∀ t, collectNumericRowParts D t = ls t) (r s : CopyLabel D) :
    integerRowsFourTrace D r s =
      (collectedFourPartsTrace D r.val.val s.val.val ls : ℚ) / fourCommonDenominator := by
  rw [integerRowsFourTrace_numeric hD]
  simp only [numericRowsFourTrace, collectedFourPartsTrace, collectNumericRowParts_sum, hls]

end LaughlinFock
end

end OAI
