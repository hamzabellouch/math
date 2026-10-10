import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.AffinePhysicalThreshold

namespace OAI

/-! Literal polynomial-time evaluation of the complete affine threshold shift.
Every precision and loop bound is computed in unary from polynomial metadata. -/

namespace ContinuumCoulomb.AffinePhysicalThreshold
open ExactQuantumFactoring.BitStackProgram

def dataCode : (ℚ×(List CoulombPairSum.Point×List ℚ)) → List Bool :=
  prodCode ratCode (prodCode (listCode CoulombPairSum.pointCode) (listCode ratCode))
def inputCode : Input → List Bool := prodCode CenteredPhysicalThreshold.inputCode dataCode

noncomputable opaque numbersProgram : Procedure inputCode CenteredPhysicalThreshold.inputCode Prod.fst :=
  Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode dataCode Prod.snd := Procedure.second _ _
noncomputable opaque tauProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp dataProgram
noncomputable opaque listsProgram : Procedure inputCode
    (prodCode (listCode CoulombPairSum.pointCode) (listCode ratCode)) (fun x => x.2.2) :=
  (Procedure.second _ _).comp dataProgram
noncomputable opaque sitesProgram : Procedure inputCode (listCode CoulombPairSum.pointCode)
    (fun x => x.2.2.1) := (Procedure.first _ _).comp listsProgram
noncomputable opaque weightsProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.2.2.2) := (Procedure.second _ _).comp listsProgram
noncomputable opaque errorProgram : Procedure inputCode unaryCode (fun x => x.1.2.2.1) :=
  CenteredPhysicalThreshold.errorProgram.comp numbersProgram
noncomputable opaque geometryProgram : Procedure inputCode CenteredPhysicalThreshold.geometryCode
    (fun x => x.1.1) := CenteredPhysicalThreshold.geometryProgram.comp numbersProgram
noncomputable opaque electronsProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  CenteredPhysicalThreshold.electronsProgram.comp numbersProgram
noncomputable opaque precisionProgram : Procedure inputCode unaryCode
    (fun x => 2*(x.1.2.2.1+1)) :=
  ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 2).pair
      (Procedure.unarySuccessor.comp errorProgram))

noncomputable opaque pairPrecisionProgram : Procedure inputCode unaryCode pairPrecision := by
  let cube := CenteredPhysicalThreshold.meshCubeProgram.comp numbersProgram
  let base := Procedure.unarySuccessor.comp (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 8).pair cube))
  exact (ResolventSchedule.mulProgram.comp (base.pair precisionProgram)).congrFun
    (by intro x; rfl)

noncomputable opaque pairProgram (rho : ℕ) : Procedure inputCode ratCode (pairValue rho) :=
  (CoulombPairSum.program rho).comp (pairPrecisionProgram.pair sitesProgram)

noncomputable opaque finiteProgram (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode)
    (finiteValue rho) := by
  let bounds := CenteredPhysicalThreshold.endpointsProgram.comp numbersProgram
  let lower := (Procedure.first ratCode ratCode).comp bounds
  let upper := (Procedure.second ratCode ratCode).comp bounds
  let sum := RationalSumProgram.sumProgram.comp weightsProgram
  let tauSquared := Procedure.ratMul.comp (tauProgram.pair tauProgram)
  let lowerShift := Procedure.ratSub.comp (lower.pair sum)
  let upperShift := Procedure.ratSub.comp (upper.pair sum)
  let lowerScale := Procedure.ratMul.comp (tauSquared.pair lowerShift)
  let upperScale := Procedure.ratMul.comp (tauSquared.pair upperShift)
  exact ((Procedure.ratSub.comp (lowerScale.pair (pairProgram rho))).pair
    (Procedure.ratSub.comp (upperScale.pair (pairProgram rho)))).congrFun
      (by intro x; simp only [finiteValue,pow_two,Function.comp_apply])

noncomputable opaque argumentProgram (rho : ℕ) :
    Procedure inputCode CenteredPhysicalThreshold.inputCode (argument rho) :=
  geometryProgram.pair (electronsProgram.pair (precisionProgram.pair (finiteProgram rho)))

noncomputable opaque program (rho : ℕ) : Procedure inputCode (prodCode ratCode ratCode) (value rho) :=
  (CenteredPhysicalThreshold.program rho).comp (argumentProgram rho)

noncomputable def certificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode (prodCode ratCode ratCode) (value rho) :=
  (program rho).toTM2

end ContinuumCoulomb.AffinePhysicalThreshold

end OAI
