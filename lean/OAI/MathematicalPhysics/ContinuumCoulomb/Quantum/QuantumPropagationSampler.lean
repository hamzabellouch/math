import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPropagationOrder

namespace OAI

/-! Literal local propagation tables after adding the single reference bit.
The arity is fixed in each program; no ambient spin configurations are scanned. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPropagationSampler
open QuantumAlgebraicScalar QuantumAlgebraicHistory QuantumFixedPauli
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode
open scoped Classical

abbrev Input := QuantumPropagationTable.Input
abbrev inputCode := QuantumPropagationTable.inputCode

def coefficient (c : QMACircuit) : ℚ := (14*(c.work+1)+8)*c.gates.length

def table (m : ℕ) (x : Input) : Matrix (Fin (m+1) → Fin 2) (Fin (m+1) → Fin 2) Scalar :=
  fun s t => oneReference (s 0) (t 0) (mul (rat (coefficient x.1))
    (matMul (adjoint (QuantumPropagationTable.table m x))
      (QuantumPropagationTable.table m x) (fun j => s j.succ) (fun j => t j.succ)))

noncomputable opaque coefficientProgram : Procedure inputCode scalarCode
    (fun x => rat (coefficient x.1)) := by
  let c := Procedure.first circuitCode (prodCode Nat.bits (listCode Nat.bits))
  let work := Procedure.unaryToBits.comp (workProgram.comp c)
  let time := Procedure.unaryToBits.comp (QuantumHistoryDescriptors.timeProgram.comp c)
  let const (n : ℕ) := Procedure.constant inputCode Nat.bits n
  let inner := Procedure.binaryAdd.comp
    ((Procedure.binaryMul.comp ((const 14).pair (Procedure.successor.comp work))).pair (const 8))
  let n := Procedure.binaryMul.comp (inner.pair time)
  exact (ratProgram.comp (Procedure.natToRat.comp n)).congrFun (by
    intro x
    simp only [coefficient,Function.comp_apply,id_eq,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
      Nat.succ_eq_add_one])

noncomputable opaque oneReferenceProgram (a b : Fin 2) :
    Procedure scalarCode scalarCode (oneReference a b) := by
  let cr := Procedure.constant scalarCode scalarCode (identity a b)
  let ci := Procedure.constant scalarCode scalarCode (QuantumFixedPauli.pauli 2 a b)
  let minusI := Procedure.constant scalarCode scalarCode (neg imaginary)
  exact (addProgram.comp
    ((mulProgram.comp (cr.pair realPartProgram)).pair
      (mulProgram.comp (minusI.pair (mulProgram.comp (ci.pair imagPartProgram)))))).congrFun
        (by intro x; rfl)

noncomputable opaque entryProgram (m : ℕ) (s t : Fin (m+1) → Fin 2) :
    Procedure inputCode scalarCode (fun x => table m x s t) := by
  let core := (QuantumFixedPauli.entryProgram (fun j : Fin m => s j.succ)
    (fun j : Fin m => t j.succ)).comp (QuantumPropagationTable.gramProgram m)
  let scaled := mulProgram.comp (coefficientProgram.pair core)
  exact ((oneReferenceProgram (s 0) (t 0)).comp scaled).congrFun (by
    intro x
    simp only [Function.comp_apply,table,entry_matrixData])

noncomputable def tableProgram (m : ℕ) : Procedure inputCode matrixCode
    (fun x => matrixData (table m x)) :=
  QuantumFixedMatrix.dataProgram (β := Fin (m+1) → Fin 2) inputCode (table m)
    (QuantumPropagationSampler.entryProgram m)

def tableList : ℕ → Input → List Scalar
  | 0 => fun _ => matrixData (fun _ _ : Fin 0 → Fin 2 => rat 0)
  | m+1 => fun x => matrixData (table m x)

noncomputable def tableListProgram (n : ℕ) : Procedure inputCode matrixCode (tableList n) := by
  cases n with
  | zero =>
    exact Procedure.constant inputCode matrixCode
      (matrixData (fun _ _ : Fin 0 → Fin 2 => rat 0))
  | succ m => exact QuantumPropagationSampler.tableProgram m

theorem matrixData_cast {n m : ℕ} (h : n=m)
    (A : Matrix (Fin m → Fin 2) (Fin m → Fin 2) Scalar) :
    matrixData (reindex ((finCongr h).arrowCongr (Equiv.refl (Fin 2))) A)=matrixData A := by
  subst m
  rfl

def basisEquiv (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    (Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) ≃
      (Fin ((QuantumPropagationSupport.sites c t).length+1) → Fin 2) :=
  (finCongr (QuantumPropagationOrder.length_eq c hT i t ht)).arrowCongr (Equiv.refl _)

theorem basisEquiv_zero (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    basisEquiv c hT i t ht s 0=QuantumPropagationOrder.referenceBit c hT i t ht s := by
  rfl

theorem basisEquiv_succ (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t)
    (s : Fin (QuantumOrderedSupport.sites c hT (.inl i)).length → Fin 2) :
    (fun j => basisEquiv c hT i t ht s j.succ)=
      QuantumPropagationOrder.localBits c hT i t ht s := by
  rfl

theorem table_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    QuantumAlgebraicHistory.orderedTable c hT (.inl i)=
      reindex (basisEquiv c hT i t ht)
        (table (QuantumPropagationSupport.sites c t).length
          (c,t.val,QuantumPropagationSupport.labels c t)) := by
  funext s r
  rw [QuantumPropagationOrder.ordered_gram_entry c hT i t ht]
  simp only [reindex,table,basisEquiv_zero,basisEquiv_succ,coefficient]

theorem tableList_actual (c : QMACircuit) (hT : 0<c.gates.length)
    (i : Fin (qmaHistoryReferenceWork c+1)) (t : Fin c.gates.length)
    (ht : qmaOrderedTermEquiv c hT (qmaFirstUseTime c) i=QuantumPropagationOrder.term c t) :
    tableList (QuantumOrderedSupport.sites c hT (.inl i)).length
        (c,t.val,QuantumPropagationSupport.labels c t)=
      matrixData (QuantumAlgebraicHistory.orderedTable c hT (.inl i)) := by
  calc
    _ = tableList ((QuantumPropagationSupport.sites c t).length+1)
        (c,t.val,QuantumPropagationSupport.labels c t) :=
      congrArg (fun n => tableList n (c,t.val,QuantumPropagationSupport.labels c t))
        (QuantumPropagationOrder.length_eq c hT i t ht)
    _ = matrixData (table (QuantumPropagationSupport.sites c t).length
        (c,t.val,QuantumPropagationSupport.labels c t)) := rfl
    _ = _ := (matrixData_cast (QuantumPropagationOrder.length_eq c hT i t ht) _).symm.trans
      (congrArg matrixData (table_actual c hT i t ht).symm)

end ContinuumCoulomb.QuantumPropagationSampler

end

end OAI
