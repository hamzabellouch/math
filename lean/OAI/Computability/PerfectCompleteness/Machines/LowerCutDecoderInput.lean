import OAI.Computability.PerfectCompleteness.Machines.HierarchicalLowerMatrixInput

namespace OAI

section

namespace PerfectCompleteness.LowerCutDecoderInput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev LowerRows (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  Fin (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) →
    HierarchicalDecoderTables.LowerH slots upper lowerLevel d

theorem backgroundOf_update (arrays : Arrays slots rows)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (fresh : LowerRows (rows := rows) slots upper lowerLevel d) :
    HierarchicalMatrixTable.backgroundOf slots upper
        (Function.update arrays (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) fresh) =
      HierarchicalLowerMatrixInput.updateBackground slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) d
        (EvaluationMatrix.ofRows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
          fresh) := by
  funext j
  by_cases hj : j = HierarchicalFrozenTables.lowerIndex upper lowerLevel d
  · subst j
    rw [HierarchicalLowerMatrixInput.updateBackground_selected,
      EvaluationMatrix.rows_ofRows]
    exact Function.update_self _ _ _
  · have hval : j.val ≠ HierarchicalLeftDecoder.LowerNode upper lowerLevel d := by
      intro h
      exact hj (Subtype.ext h)
    rw [HierarchicalLowerMatrixInput.updateBackground_other slots upper lowerLevel
      (HierarchicalMatrixTable.backgroundOf slots upper arrays) d _ j hj]
    exact Function.update_of_ne hval _ _

theorem upperMatrix_update (arrays : Arrays slots rows)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (fresh : LowerRows (rows := rows) slots upper lowerLevel d) :
    NodeEmbedding.matrix
        (Function.update arrays (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) fresh)
        upper =
      NodeEmbedding.matrix arrays upper := by
  have hne : upper ≠ HierarchicalLeftDecoder.LowerNode upper lowerLevel d :=
    (HierarchicalFrozenTables.lowerIndex upper lowerLevel d).property.symm
  unfold NodeEmbedding.matrix NodeEmbedding.embeddedRows
  rw [Function.update_of_ne hne]

def actualInput {r : Nat} (arrays : Arrays slots rows)
    (A : ManyGoodRows.RowMap (Block rows upper) r) :
    HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r :=
  ⟨HierarchicalMatrixTable.backgroundOf slots upper arrays,
    (A, A.comp (MatrixRowQuotient.projectMatrix
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays))
      (NodeEmbedding.matrix arrays upper)))⟩

theorem actualInput_update {r : Nat} (arrays : Arrays slots rows)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (fresh : LowerRows (rows := rows) slots upper lowerLevel d) :
    actualInput slots upper lowerLevel
        (Function.update arrays (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) fresh) A =
      HierarchicalLowerMatrixInput.input slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) d
        (NodeEmbedding.matrix arrays upper) A
        (EvaluationMatrix.ofRows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
          fresh) := by
  unfold actualInput
  rw [upperMatrix_update slots upper lowerLevel arrays d fresh]
  exact congrArg
    (fun background : HierarchicalMatrixTable.Background (rows := rows) slots upper =>
      (⟨background, (A, A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (NodeEmbedding.matrix arrays upper)))⟩ :
          HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r))
    (backgroundOf_update slots upper lowerLevel arrays d fresh)

end
end PerfectCompleteness.LowerCutDecoderInput

end

end OAI
