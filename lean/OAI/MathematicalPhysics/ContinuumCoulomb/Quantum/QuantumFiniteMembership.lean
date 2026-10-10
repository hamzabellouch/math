import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteProgram
import OAI.Computability.QuantumFactoring.BitStackOptions
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! Literal membership tests for the finite geometry tables used by the
140-candidate planar route selector. The Boolean fold has constant-size state. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFiniteMembership
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode

private theorem fold_or (xs : List Bool) (b : Bool) :
    xs.foldl (fun c a => a || c) b = (xs.any id || b) := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons,List.any_cons]
    rw [ih]
    cases a <;> cases b <;> simp

noncomputable opaque anyProgram : Procedure (listCode Procedure.boolCode) Procedure.boolCode
    (fun xs => xs.any id) := by
  let p := Procedure.foldList false Procedure.boolOr (Polynomial.C 1) (by
    intro xs b i
    simp only [Procedure.boolCode,List.length_singleton,Polynomial.eval_C]
    exact le_rfl)
  exact (p.comp ((Procedure.identity _).pair (Procedure.constant _ _ false))).congrFun (by
    intro xs
    simp only [Function.comp_apply,fold_or,Bool.or_false,id_eq])

noncomputable def memberProgram {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (ea : α → List Bool)
    (d : α) (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) Procedure.boolCode
      (fun x => decide (x.1 ∈ x.2)) :=
  (anyProgram.comp (Procedure.listMapWith (f := fun a b => decide (a=b)) d false eqp)).congrFun (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp)

noncomputable opaque pairEqProgram : Procedure (prodCode pairCode pairCode) Procedure.boolCode
    (fun x => decide (x.1=x.2)) := Procedure.prodEq Procedure.binaryEq Procedure.binaryEq

noncomputable opaque pairMemberProgram :
    Procedure (prodCode pairCode (listCode pairCode)) Procedure.boolCode
      (fun x => decide (x.1 ∈ x.2)) := memberProgram pairCode (0,0) pairEqProgram

end ContinuumCoulomb.QuantumFiniteMembership

end

end OAI
