import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RawDensitySample

namespace OAI

/-! Literal arithmetic and TM2 compilation of the raw localized density
sampler. The coordinate radius and requested accuracy are encoded unary. -/

namespace ContinuumCoulomb.RawDensitySample
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode (prodCode unaryCode unaryCode)
  CappedKernelProgram.tripleCode

noncomputable opaque paramsProgram : Procedure inputCode (prodCode unaryCode unaryCode) Prod.fst :=
  Procedure.first (prodCode unaryCode unaryCode) CappedKernelProgram.tripleCode

noncomputable opaque radiusProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode unaryCode).comp paramsProgram

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.2) :=
  (Procedure.second unaryCode unaryCode).comp paramsProgram

noncomputable opaque coordinatesProgram : Procedure inputCode CappedKernelProgram.tripleCode Prod.snd :=
  Procedure.second (prodCode unaryCode unaryCode) CappedKernelProgram.tripleCode

noncomputable opaque firstCoordinateProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode (prodCode ratCode ratCode)).comp coordinatesProgram

noncomputable opaque remainingCoordinatesProgram :
    Procedure inputCode (prodCode ratCode ratCode) (fun x => x.2.2) :=
  (Procedure.second ratCode (prodCode ratCode ratCode)).comp coordinatesProgram

noncomputable opaque secondCoordinateProgram : Procedure inputCode ratCode (fun x => x.2.2.1) :=
  (Procedure.first ratCode ratCode).comp remainingCoordinatesProgram

noncomputable opaque thirdCoordinateProgram : Procedure inputCode ratCode (fun x => x.2.2.2) :=
  (Procedure.second ratCode ratCode).comp remainingCoordinatesProgram

noncomputable opaque planarArgumentProgram :
    Procedure inputCode ResolventSchedule.inputCode planarArgument := by
  let r := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 2).pair radiusProgram)
  exact (r.pair precisionProgram).pair (firstCoordinateProgram.pair secondCoordinateProgram)

noncomputable opaque verticalArgumentProgram :
    Procedure inputCode GaussianPacket.inputCode verticalArgument :=
  paramsProgram.pair thirdCoordinateProgram

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (value rho) := by
  let p := rationalUnitClampProgram.comp (ResolventSchedule.program.comp planarArgumentProgram)
  let p2 := Procedure.ratMul.comp (p.pair p)
  let z := (GaussianPacket.program rho).comp verticalArgumentProgram
  exact (Procedure.ratMul.comp (p2.pair z)).congrFun (by intro x; simp only [value, pow_two]; rfl)

noncomputable def certificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode ratCode (value rho) := (program rho).toTM2

end ContinuumCoulomb.RawDensitySample

end OAI
