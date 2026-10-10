import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWalkSeek
import OAI.Computability.QuantumFactoring.BitStackListFold

namespace OAI

/-! A polynomial finite-stack implementation of the actual coarse-walk loop
erasure. Each fold output is a sublist of the processed input and initial list. -/

noncomputable section
open scoped List
namespace ContinuumCoulomb.QuantumWalkErasure
open ExactQuantumFactoring.BitStackProgram
variable {α : Type} [DecidableEq α]

noncomputable def stepProgram (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode ea (listCode ea)) (listCode ea) (fun x => step x.1 x.2) :=
  (Procedure.conditional (QuantumFiniteMembership.memberProgram ea d eqp)
    (QuantumWalkSeek.program ea d eqp) (Procedure.listCons ea)).congrFun (by
      intro x
      simp only [step,decide_eq_true_eq])

theorem fold_sublist (xs bs : List α) :
    xs.foldl (fun ys a => step a ys) bs <+ xs.reverse ++ bs := by
  induction xs generalizing bs with
  | nil => exact List.Sublist.refl _
  | cons a xs ih =>
    simp only [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    exact (ih (step a bs)).trans ((step_sublist a bs).append_left xs.reverse)

theorem fold_code_bound (ea : α → List Bool) (xs bs : List α) :
    (listCode ea (xs.foldl (fun ys a => step a ys) bs)).length ≤
      (listCode ea xs).length+(listCode ea bs).length := by
  have h := listCode_length_sublist ea (fold_sublist xs bs)
  have ha := listCode_length_append ea xs.reverse bs
  rw [listCode_length_rev] at ha
  omega

noncomputable def foldProgram (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (prodCode (listCode ea) (listCode ea)) (listCode ea)
      (fun x => x.1.foldl (fun ys a => step a ys) x.2) :=
  Procedure.foldList d (stepProgram ea d eqp) Polynomial.X (by
    intro xs bs i
    have h := fold_code_bound ea (xs.take i) bs
    have ht := listCode_length_take_le ea i xs
    simp only [Polynomial.eval_X]
    omega)

noncomputable def program (ea : α → List Bool) (d : α)
    (eqp : Procedure (prodCode ea ea) Procedure.boolCode (fun x => decide (x.1=x.2))) :
    Procedure (listCode ea) (listCode ea) erase :=
  ((foldProgram ea d eqp).comp ((Procedure.listReverse ea d).pair
    (Procedure.constant (listCode ea) (listCode ea) []))).congrFun (by
      intro xs
      simp only [Function.comp_apply,List.foldl_reverse,erase])

noncomputable def cellProgram :
    Procedure (listCode QuantumRouteCode.pairCode) (listCode QuantumRouteCode.pairCode)
      (erase : List (ℕ × ℕ) → List (ℕ × ℕ)) :=
  program QuantumRouteCode.pairCode (0,0) QuantumFiniteMembership.pairEqProgram

end ContinuumCoulomb.QuantumWalkErasure

end

end OAI
