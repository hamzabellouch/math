import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalAllDecoderTables

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLowerMatrixInput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

abbrev Matrix (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :=
  Module.Dual F2 (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) →ₗ[F2]
    Block rows (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

def updateBackground (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalMatrixTable.Background (rows := rows) slots upper :=
  Function.update background (HierarchicalFrozenTables.lowerIndex upper lowerLevel d)
    (EvaluationMatrix.rows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) X)

@[simp] theorem updateBackground_selected
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    updateBackground slots upper lowerLevel background d X
      (HierarchicalFrozenTables.lowerIndex upper lowerLevel d) =
      EvaluationMatrix.rows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) X := by
  simp only [updateBackground, Function.update_self]

theorem updateBackground_other
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d)
    (j : {j : Nodes branch n // j ≠ upper})
    (hj : j ≠ HierarchicalFrozenTables.lowerIndex upper lowerLevel d) :
    updateBackground slots upper lowerLevel background d X j = background j := by
  exact Function.update_of_ne hj _ _

@[simp] theorem testedMatrix_update
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalLeftDecoder.testedMatrix slots upper lowerLevel
      (updateBackground slots upper lowerLevel background d X) d = X := by
  unfold HierarchicalLeftDecoder.testedMatrix
  rw [updateBackground_selected, EvaluationMatrix.ofRows_rows]

theorem updateBackground_injective
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Function.Injective (updateBackground slots upper lowerLevel background d) := by
  intro X Y h
  have heq := congrArg (fun bg =>
    HierarchicalLeftDecoder.testedMatrix slots upper lowerLevel bg d) h
  simpa only [testedMatrix_update] using heq

def advice {r : Nat} (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalDecoderTables.Advice slots upper lowerLevel
      (updateBackground slots upper lowerLevel background d X) r :=
  (A, A.comp (MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel
      (updateBackground slots upper lowerLevel background d X)) upperMatrix))

def input {r : Nat} (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r :=
  ⟨updateBackground slots upper lowerLevel background d X,
    advice slots upper lowerLevel background d upperMatrix A X⟩

@[simp] theorem input_background {r : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    (input slots upper lowerLevel background d upperMatrix A X).1 =
      updateBackground slots upper lowerLevel background d X := rfl

@[simp] theorem input_testedMatrix {r : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : Matrix (rows := rows) slots upper lowerLevel d) :
    HierarchicalLeftDecoder.testedMatrix slots upper lowerLevel
      (input slots upper lowerLevel background d upperMatrix A X).1 d = X :=
  testedMatrix_update slots upper lowerLevel background d X

theorem input_injective {r : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r) :
    Function.Injective (input slots upper lowerLevel background d upperMatrix A) := by
  intro X Y h
  exact updateBackground_injective slots upper lowerLevel background d (congrArg Sigma.fst h)

end
end PerfectCompleteness.HierarchicalLowerMatrixInput

end

end OAI
