import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabBoxSchedule

namespace OAI

/-! Polynomial evaluation of rational-width slabs and of the exact centered
mesh half-widths. Bounds remain unary; the actual widths remain rational. -/

namespace ContinuumCoulomb.SlabBoxSchedule
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool :=
  prodCode SlabOriginSchedule.inputCode (prodCode ratCode ratCode)

noncomputable opaque boundsProgram : Procedure inputCode SlabOriginSchedule.inputCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque widthsProgram : Procedure inputCode (prodCode ratCode ratCode) Prod.snd :=
  Procedure.second _ _

noncomputable opaque inputProgram (rho : ℕ) : Procedure inputCode
    (RationalQuadratureProgram.inputCode SlabOriginValue.parameterCode) (input rho) := by
  let n := (SlabOriginSchedule.countProgram rho).comp boundsProgram
  let nq := Procedure.natToRat.comp (Procedure.unaryToBits.comp n)
  let q := Procedure.natToRat.comp (Procedure.unaryToBits.comp
    ((SlabOriginSchedule.capDenominatorProgram rho).comp boundsProgram))
  let cap := Procedure.ratInv.comp q
  let step := Procedure.ratDiv.comp ((Procedure.constant inputCode ratCode (2:ℚ)).pair nq)
  exact n.pair (((n.pair cap).pair widthsProgram).pair
    ((Procedure.constant inputCode ratCode (-1:ℚ)).pair step))

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (value rho) :=
  (SlabOriginValue.program (rho:ℚ)).comp (inputProgram rho)

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime inputCode ratCode
    (value rho) := (program rho).toTM2

def centeredCode : (ℕ×(ℕ×(ℕ×ℕ))) → List Bool :=
  prodCode unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))

noncomputable opaque centeredInputProgram : Procedure centeredCode inputCode
    (fun x => centered x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let p := Procedure.first unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let tail := Procedure.second unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))
  let n := (Procedure.first unaryCode (prodCode unaryCode unaryCode)).comp tail
  let box := (Procedure.second unaryCode (prodCode unaryCode unaryCode)).comp tail
  let h := (Procedure.first unaryCode unaryCode).comp box
  let s := (Procedure.second unaryCode unaryCode).comp box
  let nq := Procedure.natToRat.comp (Procedure.unaryToBits.comp n)
  let hq := Procedure.natToRat.comp (Procedure.unaryToBits.comp h)
  let sq := Procedure.natToRat.comp (Procedure.unaryToBits.comp s)
  let half := Procedure.constant centeredCode ratCode (1/2:ℚ)
  let hw := Procedure.ratDiv.comp ((Procedure.ratAdd.comp (hq.pair half)).pair nq)
  let sw := Procedure.ratDiv.comp ((Procedure.ratAdd.comp (sq.pair half)).pair nq)
  exact (p.pair ((Procedure.unarySuccessor.comp h).pair
    (Procedure.unarySuccessor.comp s))).pair (hw.pair sw)

noncomputable opaque centeredProgram (rho : ℕ) : Procedure centeredCode ratCode
    (fun x => value rho (centered x.1 x.2.1 x.2.2.1 x.2.2.2)) :=
  (program rho).comp centeredInputProgram

noncomputable def centeredCertificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime centeredCode ratCode
      (fun x => value rho (centered x.1 x.2.1 x.2.2.1 x.2.2.2)) :=
  (centeredProgram rho).toTM2

end ContinuumCoulomb.SlabBoxSchedule

end OAI
