import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRebitDiagonal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDiagonalProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedMatrixProgram

namespace OAI

/-! Fixed-arity scalar tables for the actual diagonal history terms.
Only the local support bits are tabulated; the arity is at most six. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDiagonal
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumCircuitCode QuantumHistoryDescriptors
open scoped Classical

abbrev TableInput := QMACircuit × (Descriptor × List ℕ)
def tableCode : TableInput → List Bool :=
  prodCode circuitCode (prodCode descriptorCode (listCode Nat.bits))

def tableData (n : ℕ) (s t : Fin n → Fin 2) (x : TableInput) : QuantumHistoryBitProgram.Data :=
  (x.2.2,List.ofFn (fun i => (s i).val),List.ofFn (fun i => (t i).val))

def table (n : ℕ) (x : TableInput) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar :=
  fun s t => if s=t then rat (weight x.1 x.2.1 (tableData n s t x)) else rat 0

def tableList (n : ℕ) (x : TableInput) : List Scalar := matrixData (table n x)

noncomputable opaque tableEntryInputProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure tableCode inputCode (fun x => (x.1,x.2.1,tableData n s t x)) := by
  let c := Procedure.first circuitCode (prodCode descriptorCode (listCode Nat.bits))
  let rest := Procedure.second circuitCode (prodCode descriptorCode (listCode Nat.bits))
  let a := (Procedure.first descriptorCode (listCode Nat.bits)).comp rest
  let labels := (Procedure.second descriptorCode (listCode Nat.bits)).comp rest
  let rows := Procedure.constant tableCode (listCode Nat.bits) (List.ofFn (fun i => (s i).val))
  let columns := Procedure.constant tableCode (listCode Nat.bits) (List.ofFn (fun i => (t i).val))
  exact c.pair (a.pair (labels.pair (rows.pair columns)))

noncomputable def tableEntryProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure tableCode scalarCode (fun x => table n x s t) := by
  by_cases h : s=t
  · exact (weightProgram.comp (tableEntryInputProgram n s t)).congrFun
      (by intro x; simp only [table,h,ite_true,Function.comp_apply])
  · exact (Procedure.constant tableCode scalarCode (rat 0)).congrFun
      (by intro x; simp only [table,h,ite_false])

noncomputable def tableProgram (n : ℕ) :
    Procedure tableCode matrixCode (tableList n) :=
  QuantumFixedMatrix.dataProgram tableCode (table n) (tableEntryProgram n)

theorem table_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    table (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      QuantumAlgebraicHistory.orderedTable c hT (.inl i) := by
  funext s t
  exact (ordered_diagonal_entry c hT i ha s t).symm

theorem tableList_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1))
    (ha : (encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i)).1<4) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
      (c,encode c (qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i),
        QuantumOrderedSupport.encodedSites c hT (.inl i)) =
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) :=
  congrArg matrixData (table_actual c hT i ha)

end ContinuumCoulomb.QuantumHistoryDiagonal

end

end OAI
