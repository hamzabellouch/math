import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFixedPauli
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAlgebraicScalarProgram

namespace OAI

/-! A literal polynomial evaluator for every coefficient of a fixed
local core.  Six is the largest arity used by the history construction;
the finite loops below are part of the fixed program, not the input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFixedPauli
open QuantumAlgebraicScalar ExactQuantumFactoring.BitStackProgram
open scoped Classical

-- Match the domain decision used inside the generic coefficient definition;
-- otherwise two propositionally equal Pi enumerations force proof reduction.
local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

noncomputable def finiteSumProgram {α β : Type} [Fintype β]
    (ea : α → List Bool) (f : β → α → Scalar)
    (p : ∀ i, Procedure ea scalarCode (f i)) :
    Procedure ea scalarCode (fun x => finiteSum (fun i => f i x)) :=
  (fixedSumProgram ea (Fintype.card β)
    (fun i => f ((Fintype.equivFin β).symm i))
    (fun i => p ((Fintype.equivFin β).symm i))).congrFun (by
      intro x
      simp only [finiteSum,enumerate,List.map_ofFn,Function.comp_def])

noncomputable def finiteProductProgram {α β : Type} [Fintype β]
    (ea : α → List Bool) (f : β → α → Scalar)
    (p : ∀ i, Procedure ea scalarCode (f i)) :
    Procedure ea scalarCode (fun x => finiteProduct (fun i => f i x)) :=
  (fixedProductProgram ea (Fintype.card β)
    (fun i => f ((Fintype.equivFin β).symm i))
    (fun i => p ((Fintype.equivFin β).symm i))).congrFun (by
      intro x
      simp only [finiteProduct,enumerate,List.map_ofFn,Function.comp_def])

def matrixData {β : Type} [Fintype β] (A : Matrix β β Scalar) : List Scalar :=
  (enumerate (β×β)).map (fun p => A p.1 p.2)

def entry {β : Type} [Fintype β] (xs : List Scalar) (s t : β) : Scalar :=
  (xs.drop ((Fintype.equivFin (β×β)) (s,t)).val).headD (rat 0)

theorem entry_matrixData {β : Type} [Fintype β]
    (A : Matrix β β Scalar) (s t : β) : entry (matrixData A) s t = A s t := by
  simp only [entry,matrixData,enumerate,List.map_ofFn,List.headD_eq_head?_getD,
    List.head?_drop,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some,
    Function.comp_apply,Fin.eta,Equiv.symm_apply_apply]

def matrixCode : List Scalar → List Bool := listCode scalarCode

noncomputable def entryProgram {β : Type} [Fintype β] (s t : β) :
    Procedure matrixCode scalarCode (fun xs => entry xs s t) :=
  (Procedure.listGet scalarCode (rat 0)).comp
    ((Procedure.constant matrixCode Nat.bits ((Fintype.equivFin (β×β)) (s,t)).val).pair
      (Procedure.identity matrixCode))

noncomputable opaque coefficientCellProgram (n : ℕ) (w : Fin n → Fin 4)
    (s t : Fin n → Fin 2) : Procedure matrixCode scalarCode
      (fun xs => mul (entry xs s t) (word w t s)) :=
  mulProgram.comp
    ((entryProgram s t).pair (Procedure.constant matrixCode scalarCode (word w t s)))

noncomputable opaque coefficientRowProgram (n : ℕ) (w : Fin n → Fin 4)
    (s : Fin n → Fin 2) : Procedure matrixCode scalarCode
      (fun xs => finiteSum (fun t => mul (entry xs s t) (word w t s))) :=
  finiteSumProgram matrixCode _ (coefficientCellProgram n w s)

noncomputable opaque coefficientTotalProgram (n : ℕ) (w : Fin n → Fin 4) :
    Procedure matrixCode scalarCode
      (fun xs => finiteSum (fun s : Fin n → Fin 2 =>
        finiteSum (fun t => mul (entry xs s t) (word w t s)))) :=
  finiteSumProgram matrixCode _ (coefficientRowProgram n w)

noncomputable opaque coefficientProgram (n : ℕ) (w : Fin n → Fin 4) :
    Procedure matrixCode scalarCode
      (fun xs => coefficient (fun s t : Fin n → Fin 2 => entry xs s t) w) := by
  let c : Scalar := rat (((2:ℚ)^Fintype.card (Fin n))⁻¹)
  let pc : Procedure matrixCode scalarCode (fun _ => c) :=
    Procedure.constant matrixCode scalarCode c
  let pt := coefficientTotalProgram n w
  let pp : Procedure matrixCode (prodCode scalarCode scalarCode)
      (fun xs => (c,finiteSum (fun s : Fin n → Fin 2 =>
        finiteSum (fun t => mul (entry xs s t) (word w t s))))) := pc.pair pt
  exact (mulProgram.comp pp).congrFun (by intro xs; rfl)

noncomputable def realCoefficientProgram (n : ℕ) (w : Fin n → Fin 4) :
    Procedure matrixCode realCode
      (fun xs => realCoefficient (fun s t : Fin n → Fin 2 => entry xs s t) w) :=
  (Procedure.first realCode realCode).comp (coefficientProgram n w)

def coefficients (n : ℕ) (xs : List Scalar) : List RealScalar :=
  (enumerate (Fin n → Fin 4)).map
    (fun w => realCoefficient (fun s t : Fin n → Fin 2 => entry xs s t) w)

noncomputable def coefficientsProgram (n : ℕ) :
    Procedure matrixCode (listCode realCode) (coefficients n) :=
  (QuantumRawExchange.fixedListProgram matrixCode realCode
    (Fintype.card (Fin n → Fin 4))
    (fun i xs => realCoefficient (fun s t : Fin n → Fin 2 => entry xs s t)
      ((Fintype.equivFin (Fin n → Fin 4)).symm i))
    (fun i => realCoefficientProgram n ((Fintype.equivFin (Fin n → Fin 4)).symm i))).congrFun
      (by intro xs; simp only [coefficients,enumerate,List.map_ofFn,Function.comp_def])

theorem coefficient_matrixData (n : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar) (w : Fin n → Fin 4) :
    realValue (realCoefficient (fun s t => entry (matrixData A) s t) w) =
      (qmaPauliCoefficient (fun s t => value (A s t)) w).re := by
  have he : (fun s t => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  rw [he]
  exact realCoefficient_eq A w

noncomputable def certificate (n : ℕ) :
    Turing.TM2ComputableInPolyTime matrixCode (listCode realCode) (coefficients n) :=
  (coefficientsProgram n).toTM2

end ContinuumCoulomb.QuantumFixedPauli

end

end OAI
