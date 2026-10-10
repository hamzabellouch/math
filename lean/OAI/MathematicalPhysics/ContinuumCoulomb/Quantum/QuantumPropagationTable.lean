import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPropagationSupport
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryDeltaProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedMatrixProgram

namespace OAI

/-! Exact fixed-size propagation tables and their adjoint-product.  The
largest table has five qubits, independently of the circuit work register. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationTable
open ExactQuantumFactoring.BitStackProgram QuantumAlgebraicScalar QuantumFixedPauli
open QuantumAlgebraicHistory QuantumCircuitCode
open scoped Classical

abbrev Input := QMACircuit × (ℕ × List ℕ)
def inputCode : Input → List Bool :=
  prodCode circuitCode (prodCode Nat.bits (listCode Nat.bits))

def data (n : ℕ) (s t : Fin n → Fin 2) (x : Input) : QuantumHistoryBitProgram.Data :=
  (x.2.2,List.ofFn (fun i => (s i).val),List.ofFn (fun i => (t i).val))

def table (n : ℕ) (x : Input) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar :=
  fun s t => QuantumHistoryDelta.entry x.1 x.2.1 (data n s t x)

noncomputable opaque entryInputProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode QuantumHistoryDiagonal.inputCode
      (fun x => (x.1,(4,x.2.1),data n s t x)) := by
  let c := Procedure.first circuitCode (prodCode Nat.bits (listCode Nat.bits))
  let tail := Procedure.second circuitCode (prodCode Nat.bits (listCode Nat.bits))
  let time := (Procedure.first Nat.bits (listCode Nat.bits)).comp tail
  let labels := (Procedure.second Nat.bits (listCode Nat.bits)).comp tail
  let a := (Procedure.constant inputCode Nat.bits 4).pair time
  let rows := Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun i => (s i).val))
  let columns := Procedure.constant inputCode (listCode Nat.bits) (List.ofFn (fun i => (t i).val))
  exact c.pair (a.pair (labels.pair (rows.pair columns)))

noncomputable opaque entryProgram (n : ℕ) (s t : Fin n → Fin 2) :
    Procedure inputCode scalarCode (fun x => table n x s t) :=
  (QuantumHistoryDelta.program.comp (entryInputProgram n s t)).congrFun
    (by intro x; rfl)

noncomputable def tableProgram (n : ℕ) :
    Procedure inputCode matrixCode (fun x => matrixData (table n x)) :=
  QuantumFixedMatrix.dataProgram (β := Fin n → Fin 2) inputCode (table n)
    (QuantumPropagationTable.entryProgram n)

noncomputable def gramProgram (n : ℕ) : Procedure inputCode matrixCode
    (fun x => matrixData (matMul (adjoint (table n x)) (table n x))) :=
  ((QuantumFixedMatrix.gramProgram (Fin n → Fin 2)).comp
    (QuantumPropagationTable.tableProgram n)).congrFun
    (by intro x; exact QuantumFixedMatrix.gramData_matrixData (table n x))

def supportBasisEquiv (c : QMACircuit) (t : Fin c.gates.length) :
    (Fin (QuantumPropagationSupport.sites c t).length → Fin 2) ≃
      QMASupportBasis (qmaPropagationSites c t) :=
  (QuantumPropagationSupport.supportEquiv c t).arrowCongr (Equiv.refl (Fin 2))

theorem table_actual (c : QMACircuit) (t : Fin c.gates.length) :
    table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)=
      reindex (supportBasisEquiv c t) (deltaCore c t) := by
  funext s r
  change QuantumHistoryDelta.entry c t.val (QuantumPropagationSupport.data c t s r)=_
  rw [QuantumHistoryDelta.entry_actual,QuantumPropagationSupport.readRow_actual,
    QuantumPropagationSupport.readColumn_actual]
  rfl

theorem gram_actual (c : QMACircuit) (t : Fin c.gates.length) :
    matMul (adjoint (table (QuantumPropagationSupport.sites c t).length
      (c,t.val,QuantumPropagationSupport.labels c t)))
      (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t))=
      reindex (supportBasisEquiv c t) (propagationCore c t) := by
  rw [table_actual,gram_reindex]
  rfl

theorem gramData_actual (c : QMACircuit) (t : Fin c.gates.length) :
    QuantumFixedMatrix.gramData (β := Fin (QuantumPropagationSupport.sites c t).length → Fin 2)
      (matrixData (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t)))=
      matrixData (reindex (supportBasisEquiv c t) (propagationCore c t)) := by
  rw [QuantumFixedMatrix.gramData_matrixData,gram_actual]

end ContinuumCoulomb.QuantumPropagationTable

end

end OAI
