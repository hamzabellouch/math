import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HoppingSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.NormalizationProgram

namespace OAI

/-! A literal polynomial TM2 program for the contact numerator, with
unary displacement bound and inverse-accuracy parameter. -/

namespace ContinuumCoulomb.HoppingSchedule
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode (prodCode unaryCode unaryCode) ratCode

noncomputable opaque meshFactorsProgram : Procedure unaryCode (prodCode unaryCode unaryCode)
    (fun P => (4096, P + 1)) :=
  NormalizationSchedule.constant4096Program.pair Procedure.unarySuccessor

noncomputable opaque meshRawProgram : Procedure unaryCode unaryCode
    (fun P => 4096 * (P + 1)) := ResolventSchedule.mulProgram.comp meshFactorsProgram

noncomputable opaque meshProgram : Procedure unaryCode unaryCode mesh :=
  meshRawProgram.congrFun (by intro P; rfl)

noncomputable opaque accuracyProgram : Procedure unaryCode unaryCode accuracy :=
  ResolventSchedule.scaleProgram

noncomputable opaque argumentProgram :
    Procedure inputCode (RationalRectangleProgram.inputCode HoppingQuadrature.settingsCode) argument := by
  let rp := Procedure.first (prodCode unaryCode unaryCode) ratCode
  let r := (Procedure.first unaryCode unaryCode).comp rp
  let p := (Procedure.second unaryCode unaryCode).comp rp
  let d := Procedure.second (prodCode unaryCode unaryCode) ratCode
  let n := meshProgram.comp p
  let a := accuracyProgram.comp p
  let r2 := ResolventSchedule.addProgram.comp (r.pair (Procedure.constant inputCode unaryCode 2))
  let nr := Procedure.natToRat.comp (Procedure.unaryToBits.comp n)
  let step := Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode 2).pair nr)
  let lower := Procedure.constant inputCode ratCode (-1)
  exact (n.pair (((r2.pair a).pair d).pair (lower.pair step))).congrFun (by intro x; rfl)

noncomputable opaque program : Procedure inputCode ratCode approximate :=
  (HoppingQuadrature.program.comp argumentProgram).congrFun (by intro x; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode ratCode approximate := program.toTM2

end ContinuumCoulomb.HoppingSchedule

end OAI
