import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianFrequency

namespace OAI

/-! Literal arithmetic for the fixed-density Gaussian frequency evaluator. -/

namespace ContinuumCoulomb.GaussianFrequency
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque countProgram (rho : ℕ) : Procedure unaryCode unaryCode (count rho) := by
  let sq := ResolventSchedule.squareProgram.comp Procedure.unarySuccessor
  let c := Procedure.constant unaryCode unaryCode (512 * (rho + 1))
  exact (ResolventSchedule.mulProgram.comp (c.pair sq)).congrFun (by intro P; rfl)

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode precision :=
  (ResolventSchedule.mulProgram.comp
    ((Procedure.constant unaryCode unaryCode 8).pair Procedure.unarySuccessor)).congrFun
      (by intro P; rfl)

noncomputable opaque radicandProgram (rho : ℕ) : Procedure unaryCode ratCode (radicand rho) := by
  let p := PiProgram.program.comp (countProgram rho)
  let c := Procedure.constant unaryCode ratCode (4 * (rho : ℚ))
  exact (Procedure.ratMul.comp (c.pair p)).congrFun (by intro P; rfl)

noncomputable opaque program (rho : ℕ) : Procedure unaryCode ratCode (approximate rho) :=
  (RationalSquareRoot.program.comp (precisionProgram.pair (radicandProgram rho))).congrFun
    (by intro P; rfl)

noncomputable def certificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime unaryCode ratCode (approximate rho) := (program rho).toTM2

end ContinuumCoulomb.GaussianFrequency

end OAI
