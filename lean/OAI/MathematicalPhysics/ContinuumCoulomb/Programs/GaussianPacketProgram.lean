import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianPacket

namespace OAI

/-! The fixed-frequency Gaussian sample has an actual polynomial-time
Turing program. Both its frequency computation and its exponential
computation use explicit polynomial unary precision schedules. -/

namespace ContinuumCoulomb.GaussianPacket
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode (prodCode unaryCode unaryCode) ratCode

noncomputable opaque radiusProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode unaryCode).comp
    (Procedure.first (prodCode unaryCode unaryCode) ratCode)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.2) :=
  (Procedure.second unaryCode unaryCode).comp
    (Procedure.first (prodCode unaryCode unaryCode) ratCode)

noncomputable opaque pointProgram : Procedure inputCode ratCode Prod.snd :=
  Procedure.second (prodCode unaryCode unaryCode) ratCode

noncomputable opaque radiusSquareProgram : Procedure inputCode unaryCode (fun x => (x.1.1 + 1) ^ 2) :=
  ResolventSchedule.squareProgram.comp (Procedure.unarySuccessor.comp radiusProgram)

noncomputable opaque frequencyPrecisionProgram : Procedure inputCode unaryCode
    (fun x => frequencyPrecision x.1.1 x.1.2) := by
  let scaled := ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 16).pair radiusSquareProgram)
  exact (ResolventSchedule.mulProgram.comp
    (scaled.pair (Procedure.unarySuccessor.comp precisionProgram))).congrFun
      (by intro x; rfl)

noncomputable opaque frequencyProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => GaussianFrequency.approximate rho (frequencyPrecision x.1.1 x.1.2)) :=
  (GaussianFrequency.program rho).comp frequencyPrecisionProgram

noncomputable opaque exponentProgram (rho : ℕ) : Procedure inputCode ratCode (exponent rho) := by
  let neg := Procedure.ratNeg.comp (frequencyProgram rho)
  let square := Procedure.ratMul.comp (pointProgram.pair pointProgram)
  exact (Procedure.ratMul.comp (neg.pair square)).congrFun
    (by intro x; simp only [exponent, Function.comp_apply, pow_two])

noncomputable opaque magnitudeProgram (rho : ℕ) : Procedure inputCode unaryCode
    (fun x => magnitude rho x.1.1) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode (4 * rho + 4)).pair radiusSquareProgram)).congrFun
      (by intro x; rfl)

noncomputable opaque exponentialPrecisionProgram : Procedure inputCode unaryCode
    (fun x => exponentialPrecision x.1.2) :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant inputCode unaryCode 8).pair
      (Procedure.unarySuccessor.comp precisionProgram))).congrFun (by intro x; rfl)

noncomputable opaque argumentProgram (rho : ℕ) :
    Procedure inputCode RationalExponentialProgram.inputCode (argument rho) :=
  (magnitudeProgram rho).pair (exponentialPrecisionProgram.pair (exponentProgram rho))

noncomputable opaque program (rho : ℕ) : Procedure inputCode ratCode (approximate rho) :=
  (rationalUnitClampProgram.comp
    (RationalExponentialProgram.program.comp (argumentProgram rho))).congrFun (by intro x; rfl)

noncomputable def certificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode ratCode (approximate rho) :=
  (program rho).toTM2

end ContinuumCoulomb.GaussianPacket

end OAI
