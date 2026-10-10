import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabOriginSchedule

namespace OAI

/-! Literal polynomial-time program for the slab origin potential. -/

namespace ContinuumCoulomb.SlabOriginSchedule
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque boxProgram : Procedure inputCode (prodCode unaryCode unaryCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque horizontalProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp boxProgram
noncomputable opaque verticalProgram : Procedure inputCode unaryCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp boxProgram

noncomputable opaque capDenominatorProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => capDenominator rho x.1) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode (16*(rho+1))).pair
      (Procedure.unarySuccessor.comp precisionProgram))).congrFun (by intro x; rfl)

noncomputable opaque boxWeightProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => boxWeight rho x.2.1 x.2.2) := by
  let hp := Procedure.unarySuccessor.comp horizontalProgram
  let hs := ResolventSchedule.squareProgram.comp hp
  let sp := Procedure.unarySuccessor.comp verticalProgram
  let total := Procedure.unarySuccessor.comp
    (ResolventSchedule.addProgram.comp (horizontalProgram.pair verticalProgram))
  let first := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode (rho+1)).pair hs)
  let second := ResolventSchedule.mulProgram.comp (first.pair sp)
  exact (ResolventSchedule.mulProgram.comp (second.pair total)).congrFun (by intro x; rfl)

noncomputable opaque countProgram (rho : ℕ) : Procedure inputCode unaryCode (count rho) := by
  let first := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 128).pair (boxWeightProgram rho))
  let second := ResolventSchedule.mulProgram.comp
    (first.pair (Procedure.unarySuccessor.comp precisionProgram))
  let sq := ResolventSchedule.squareProgram.comp (capDenominatorProgram rho)
  exact (ResolventSchedule.mulProgram.comp (second.pair sq)).congrFun (by intro x; rfl)

noncomputable opaque inputProgram (rho : ℕ) : Procedure inputCode
    (RationalQuadratureProgram.inputCode SlabOriginValue.parameterCode) (input rho) := by
  let n := countProgram rho
  let nq := Procedure.natToRat.comp (Procedure.unaryToBits.comp n)
  let q := Procedure.natToRat.comp (Procedure.unaryToBits.comp (capDenominatorProgram rho))
  let cap := Procedure.ratInv.comp q
  let hq := Procedure.natToRat.comp (Procedure.unaryToBits.comp horizontalProgram)
  let sq := Procedure.natToRat.comp (Procedure.unaryToBits.comp verticalProgram)
  let step := Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode (2:ℚ)).pair nq)
  let start := Procedure.constant inputCode ratCode (-1:ℚ)
  exact n.pair (((n.pair cap).pair (hq.pair sq)).pair (start.pair step))

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (value rho) :=
  (SlabOriginValue.program (rho:ℚ)).comp (inputProgram rho)

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime inputCode ratCode
    (value rho) := (program rho).toTM2

end ContinuumCoulomb.SlabOriginSchedule

end OAI
