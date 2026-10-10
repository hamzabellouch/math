import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CountertermEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalSumProgram
import OAI.Computability.QuantumFactoring.BitStackListMapWith

namespace OAI

/-! Literal polynomial programs evaluate the exact counterterm formula
with the error certified in CountertermEvaluation. -/

namespace ContinuumCoulomb.CountertermEvaluation
open ExactQuantumFactoring.BitStackProgram

abbrev EntryInput := CoulombPairEvaluation.Input
abbrev RowInput := ℕ×((ℚ×ℚ)×List (ℚ×ℚ))
def rowCode : RowInput → List Bool := prodCode unaryCode
  (prodCode CoulombPairEvaluation.pointCode (listCode CoulombPairEvaluation.pointCode))

noncomputable opaque maxOneProgram : Procedure ratCode ratCode (fun q => max 1 q) := by
  let one := Procedure.constant ratCode ratCode (1:ℚ)
  let q := Procedure.identity ratCode
  let test := Procedure.intSign.comp (Procedure.ratNum.comp (Procedure.ratSub.comp (q.pair one)))
  exact (Procedure.conditional test one q).congrFun (by
    intro q
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq]
    by_cases h : q < 1
    · rw [ite_eq_left (by linarith),max_eq_left h.le]
    · rw [ite_eq_right (by linarith),max_eq_right (le_of_not_gt h)])

noncomputable opaque onsiteArgumentProgram : Procedure unaryCode HoppingSchedule.inputCode
    (fun p => ((1,p),0)) := by
  let p := Procedure.identity unaryCode
  let r := Procedure.constant unaryCode unaryCode 1
  let z := Procedure.constant unaryCode ratCode (0:ℚ)
  exact (r.pair p).pair z

noncomputable opaque onsiteProgram : Procedure unaryCode ratCode
    (fun p => ComputableHopping.approximate ((1,p),0)) :=
  ComputableHopping.program.comp onsiteArgumentProgram

noncomputable opaque guardProgram (rho : ℕ) : Procedure unaryCode ratCode
    (fun _ => (guard rho:ℚ)) := Procedure.constant unaryCode ratCode (guard rho:ℚ)

noncomputable opaque scaledOnsiteProgram (rho : ℕ) : Procedure unaryCode ratCode
    (fun p => (guard rho:ℚ)*ComputableHopping.approximate ((1,p),0)) :=
  Procedure.ratMul.comp ((guardProgram rho).pair onsiteProgram)

noncomputable opaque denominatorProgram (rho : ℕ) : Procedure unaryCode ratCode (denominator rho) :=
  maxOneProgram.comp (scaledOnsiteProgram rho)

noncomputable opaque entryNumeratorProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => (guard rho:ℚ)*CoulombPairEvaluation.approximate rho x.1 x.2.1 x.2.2) := by
  let C := Procedure.constant CoulombPairEvaluation.inputCode ratCode (guard rho:ℚ)
  exact Procedure.ratMul.comp (C.pair (CoulombPairEvaluation.program rho))

noncomputable opaque entryDenominatorProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => denominator rho x.1) :=
  (denominatorProgram rho).comp (Procedure.first unaryCode CoulombPairEvaluation.pairCode)

noncomputable opaque entryArgumentsProgram (rho : ℕ) :
    Procedure CoulombPairEvaluation.inputCode (prodCode ratCode ratCode)
      (fun x => ((guard rho:ℚ)*CoulombPairEvaluation.approximate rho x.1 x.2.1 x.2.2,
        denominator rho x.1)) :=
  (entryNumeratorProgram rho).pair (entryDenominatorProgram rho)

noncomputable opaque entryProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => entry rho x.1 x.2.1 x.2.2) :=
  Procedure.ratDiv.comp (entryArgumentsProgram rho)

noncomputable opaque offsiteProgram (rho : ℕ) : Procedure CoulombPairEvaluation.inputCode ratCode
    (fun x => offsite rho x.1 x.2.1 x.2.2) := by
  let pairs := Procedure.second unaryCode CoulombPairEvaluation.pairCode
  let dist := CoulombPairEvaluation.squaredDistanceProgram.comp pairs
  let test := Procedure.binaryZero.comp (Procedure.intAbs.comp (Procedure.ratNum.comp dist))
  let zero := Procedure.constant CoulombPairEvaluation.inputCode ratCode (0:ℚ)
  exact (Procedure.conditional test zero (entryProgram rho)).congrFun (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq,Int.natAbs_eq_zero,Rat.num_eq_zero,offsite])

noncomputable opaque offsiteEnvironmentProgram (rho : ℕ) :
    Procedure (prodCode (prodCode unaryCode CoulombPairEvaluation.pointCode)
      CoulombPairEvaluation.pointCode) ratCode (fun x => offsite rho x.1.1 x.1.2 x.2) := by
  let env := Procedure.first (prodCode unaryCode CoulombPairEvaluation.pointCode)
    CoulombPairEvaluation.pointCode
  let p := (Procedure.first unaryCode CoulombPairEvaluation.pointCode).comp env
  let a := (Procedure.second unaryCode CoulombPairEvaluation.pointCode).comp env
  let b := Procedure.second (prodCode unaryCode CoulombPairEvaluation.pointCode)
    CoulombPairEvaluation.pointCode
  exact (offsiteProgram rho).comp (p.pair (a.pair b))

noncomputable opaque rowProgram (rho : ℕ) : Procedure rowCode ratCode
    (fun x => row rho x.1 x.2.1 x.2.2) := by
  let p := Procedure.first unaryCode
    (prodCode CoulombPairEvaluation.pointCode (listCode CoulombPairEvaluation.pointCode))
  let tail := Procedure.second unaryCode
    (prodCode CoulombPairEvaluation.pointCode (listCode CoulombPairEvaluation.pointCode))
  let a := (Procedure.first CoulombPairEvaluation.pointCode
    (listCode CoulombPairEvaluation.pointCode)).comp tail
  let sites := (Procedure.second CoulombPairEvaluation.pointCode
    (listCode CoulombPairEvaluation.pointCode)).comp tail
  let mapped := (Procedure.listMapWith (ea := prodCode unaryCode CoulombPairEvaluation.pointCode)
    (eb := CoulombPairEvaluation.pointCode) (ec := ratCode)
    (f := fun env b => offsite rho env.1 env.2 b) (0,0) 0
    (offsiteEnvironmentProgram rho)).comp ((p.pair a).pair sites)
  exact (RationalSumProgram.sumProgram.comp mapped).congrFun (by intro x; rfl)

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime rowCode ratCode
    (fun x => row rho x.1 x.2.1 x.2.2) := (rowProgram rho).toTM2

end ContinuumCoulomb.CountertermEvaluation

end OAI
