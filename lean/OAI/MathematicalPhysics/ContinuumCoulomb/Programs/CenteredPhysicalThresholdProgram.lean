import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CenteredPhysicalThreshold

namespace OAI

/-! Polynomial-time arithmetic for the complete physical threshold pair. -/

namespace ContinuumCoulomb.CenteredPhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

def geometryCode : Geometry → List Bool := prodCode unaryCode (prodCode unaryCode unaryCode)
def metadataCode : (ℕ×(ℕ×(ℚ×ℚ))) → List Bool :=
  prodCode unaryCode (prodCode unaryCode (prodCode ratCode ratCode))
def inputCode : Input → List Bool := prodCode geometryCode metadataCode

noncomputable opaque geometryProgram : Procedure inputCode geometryCode Prod.fst := Procedure.first _ _
noncomputable opaque metadataProgram : Procedure inputCode metadataCode Prod.snd := Procedure.second _ _
noncomputable opaque meshProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first _ _).comp geometryProgram
noncomputable opaque boxProgram : Procedure inputCode (prodCode unaryCode unaryCode)
    (fun x => x.1.2) := (Procedure.second _ _).comp geometryProgram
noncomputable opaque electronsProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp metadataProgram
noncomputable opaque restProgram : Procedure inputCode (prodCode unaryCode (prodCode ratCode ratCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp metadataProgram
noncomputable opaque errorProgram : Procedure inputCode unaryCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp restProgram
noncomputable opaque endpointsProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.2.2) := (Procedure.second _ _).comp restProgram

noncomputable opaque meshCubeProgram : Procedure inputCode unaryCode (fun x => x.1.1^3) :=
  (ResolventSchedule.mulProgram.comp
    ((ResolventSchedule.squareProgram.comp meshProgram).pair meshProgram)).congrFun
      (by intro x; dsimp; ring)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode precision := by
  let c8 := Procedure.constant inputCode unaryCode 8
  let scale := ResolventSchedule.mulProgram.comp (c8.pair meshCubeProgram)
  let sq := ResolventSchedule.squareProgram.comp (Procedure.unarySuccessor.comp scale)
  let first := ResolventSchedule.mulProgram.comp (c8.pair sq)
  let second := ResolventSchedule.mulProgram.comp
    (first.pair (Procedure.unarySuccessor.comp electronsProgram))
  exact (ResolventSchedule.mulProgram.comp
    (second.pair (Procedure.unarySuccessor.comp errorProgram))).congrFun (by intro x; rfl)

noncomputable opaque amplificationProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => amplification rho x.1.1) := by
  let cube := Procedure.natToRat.comp (Procedure.unaryToBits.comp meshCubeProgram)
  let num := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode 8).pair cube)
  exact (Procedure.ratDiv.comp
    (num.pair (Procedure.constant inputCode ratCode (rho:ℚ)))).congrFun
      (by intro x; simp [amplification])

noncomputable opaque referenceProgram (rho : ℕ) : Procedure inputCode ratCode (reference rho) := by
  let slab := (SlabBoxSchedule.centeredProgram rho).comp (precisionProgram.pair geometryProgram)
  let freq := (GaussianFrequency.program rho).comp precisionProgram
  let sub := Procedure.ratSub.comp (freq.pair (Procedure.constant inputCode ratCode 1))
  let e0 := Procedure.ratDiv.comp (sub.pair (Procedure.constant inputCode ratCode 2))
  exact (Procedure.ratAdd.comp (slab.pair e0)).congrFun (by intro x; rfl)

noncomputable opaque offsetProgram (rho : ℕ) : Procedure inputCode ratCode (offset rho) := by
  let lambda := amplificationProgram rho
  let square := Procedure.ratMul.comp (lambda.pair lambda)
  let n := Procedure.natToRat.comp (Procedure.unaryToBits.comp electronsProgram)
  let factor := Procedure.ratMul.comp (square.pair n)
  exact (Procedure.ratMul.comp (factor.pair (referenceProgram rho))).congrFun
    (by intro x; simp only [offset,pow_two,Function.comp_apply,id_eq])

noncomputable opaque program (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode) (value rho) := by
  let endpoints := endpointsProgram
  let a := (Procedure.first ratCode ratCode).comp endpoints
  let b := (Procedure.second ratCode ratCode).comp endpoints
  let lower := Procedure.ratAdd.comp
    ((offsetProgram rho).pair (Procedure.ratMul.comp ((amplificationProgram rho).pair a)))
  let upper := Procedure.ratAdd.comp
    ((offsetProgram rho).pair (Procedure.ratMul.comp ((amplificationProgram rho).pair b)))
  exact lower.pair upper

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime inputCode
    (prodCode ratCode ratCode) (value rho) := (program rho).toTM2

end ContinuumCoulomb.CenteredPhysicalThreshold

end OAI
