import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedPauliProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCoefficient

namespace OAI

/-! Literal arithmetic on a fixed local matrix table.  These templates implement
the adjoint-product and realification used in the actual history cores; their
matrix dimensions are fixed before the program receives its rational registers. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedMatrix
open QuantumFixedPauli QuantumAlgebraicScalar QuantumAlgebraicHistory
open ExactQuantumFactoring.BitStackProgram
open scoped Classical

noncomputable def dataProgram {α β : Type} [Fintype β] (ea : α → List Bool)
    (A : α → Matrix β β Scalar)
    (p : ∀ s t, Procedure ea scalarCode (fun x => A x s t)) :
    Procedure ea matrixCode (fun x => matrixData (A x)) :=
  (QuantumRawExchange.fixedListProgram ea scalarCode (Fintype.card (β×β))
    (fun i x => A x ((Fintype.equivFin (β×β)).symm i).1
      ((Fintype.equivFin (β×β)).symm i).2)
    (fun i => p _ _)).congrFun (by
      intro x
      simp only [matrixData,enumerate,List.map_ofFn,Function.comp_def])

def gramData {β : Type} [Fintype β] (xs : List Scalar) : List Scalar :=
  matrixData (matMul (adjoint (fun s t : β => entry xs s t)) (fun s t : β => entry xs s t))

noncomputable opaque gramCellProgram {β : Type} [Fintype β] (s t u : β) :
    Procedure matrixCode scalarCode (fun xs => mul (conj (entry xs u s)) (entry xs u t)) :=
  mulProgram.comp ((conjProgram.comp (entryProgram u s)).pair (entryProgram u t))

noncomputable opaque gramEntryProgram {β : Type} [Fintype β] (s t : β) :
    Procedure matrixCode scalarCode
      (fun xs => matMul (adjoint (fun a b : β => entry xs a b))
        (fun a b : β => entry xs a b) s t) :=
  finiteSumProgram matrixCode _ (fun u => gramCellProgram s t u)

noncomputable def gramProgram (β : Type) [Fintype β] :
    Procedure matrixCode matrixCode (gramData (β := β)) :=
  dataProgram matrixCode _ gramEntryProgram

theorem gramData_matrixData {β : Type} [Fintype β] (A : Matrix β β Scalar) :
    gramData (β := β) (matrixData A) = matrixData (matMul (adjoint A) A) := by
  have h : (fun s t : β => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  simp only [gramData,h]

theorem propagationData (c : QMACircuit) (t : Fin c.gates.length) :
    gramData (β := QMASupportBasis (qmaPropagationSites c t)) (matrixData (deltaCore c t)) =
      matrixData (propagationCore c t) := gramData_matrixData _

def rebitData (n : ℕ) (xs : List Scalar) : List Scalar :=
  matrixData (rebit 1 0 (fun s t : Fin n → Fin 2 => entry xs s t))

noncomputable opaque rebitEntryProgram (n : ℕ)
    (s t : Fin 1 ⊕ Fin n → Fin 2) : Procedure matrixCode scalarCode
      (fun xs => rebit 1 0 (fun a b : Fin n → Fin 2 => entry xs a b) s t) := by
  let pa := entryProgram (s ∘ Sum.inr) (t ∘ Sum.inr)
  let pr := realPartProgram.comp pa
  let pi := imagPartProgram.comp pa
  let cr := identity (s ∘ Sum.inl) (t ∘ Sum.inl)
  let ci := localY 1 0 (s ∘ Sum.inl) (t ∘ Sum.inl)
  exact (addProgram.comp
    ((mulProgram.comp ((Procedure.constant matrixCode scalarCode cr).pair pr)).pair
      (mulProgram.comp ((Procedure.constant matrixCode scalarCode (neg imaginary)).pair
        (mulProgram.comp ((Procedure.constant matrixCode scalarCode ci).pair pi)))))).congrFun (by
        intro xs
        simp only [rebit,cr,ci,Function.comp_apply]
        )

noncomputable def rebitProgram (n : ℕ) : Procedure matrixCode matrixCode (rebitData n) :=
  dataProgram matrixCode _ (rebitEntryProgram n)

theorem rebitData_matrixData (n : ℕ) (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar) :
    rebitData n (matrixData A) = matrixData (rebit 1 0 A) := by
  have h : (fun s t : Fin n → Fin 2 => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  simp only [rebitData,h]

end ContinuumCoulomb.QuantumFixedMatrix

end

end OAI
