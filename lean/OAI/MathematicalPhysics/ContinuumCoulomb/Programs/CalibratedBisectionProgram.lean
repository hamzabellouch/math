import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisectionSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisectionMachine

namespace OAI

/-! One polynomial TM2 program selects both the internal precision and
the iteration count and runs the actual calibrated bisection. -/

namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

abbrev ScheduledInput := Environment × (ℚ × ℚ)
def scheduledInputCode : ScheduledInput → List Bool :=
  prodCode environmentCode (prodCode ratCode ratCode)

noncomputable opaque envMetadataProgram : Procedure environmentCode
    (prodCode unaryCode unaryCode) Prod.fst :=
  Procedure.first (prodCode unaryCode unaryCode) (prodCode unaryCode (prodCode ratCode ratCode))
noncomputable opaque envParametersProgram : Procedure environmentCode
    (prodCode unaryCode (prodCode ratCode ratCode)) Prod.snd :=
  Procedure.second (prodCode unaryCode unaryCode) (prodCode unaryCode (prodCode ratCode ratCode))
noncomputable opaque envBoundProgram : Procedure environmentCode unaryCode (fun e => e.1.1) :=
  (Procedure.first unaryCode unaryCode).comp envMetadataProgram
noncomputable opaque envPrecisionProgram : Procedure environmentCode unaryCode (fun e => e.1.2) :=
  (Procedure.second unaryCode unaryCode).comp envMetadataProgram
noncomputable opaque envScaleProgram : Procedure environmentCode unaryCode (fun e => e.2.1) :=
  (Procedure.first unaryCode (prodCode ratCode ratCode)).comp envParametersProgram

noncomputable opaque refinedEnvironmentProgram : Procedure environmentCode environmentCode
    refinedEnvironment :=
  (envBoundProgram.pair
    (((CoulombEvaluation.scaleProgram 8).comp Procedure.unarySuccessor).comp envPrecisionProgram)).pair
      envParametersProgram

noncomputable opaque firstIterationFactorProgram (rho : ℕ) : Procedure environmentCode unaryCode
    (fun e => 16 * lipschitzGuard rho * (e.2.1 + e.1.1 + 1)) := by
  let sum := ResolventSchedule.addProgram.comp (envScaleProgram.pair envBoundProgram)
  let suc := Procedure.unarySuccessor.comp sum
  exact ((CoulombEvaluation.scaleProgram (16 * lipschitzGuard rho)).comp suc).congrFun
    (by intro e; rfl)

noncomputable opaque secondIterationFactorProgram (rho : ℕ) : Procedure environmentCode unaryCode
    (fun e => 16 * lipschitzGuard rho * (e.2.1 + e.1.1 + 1) * (e.1.1 + 1)) :=
  (ResolventSchedule.mulProgram.comp ((firstIterationFactorProgram rho).pair
    (Procedure.unarySuccessor.comp envBoundProgram))).congrFun (by intro e; rfl)

noncomputable opaque iterationsProgram (rho : ℕ) : Procedure environmentCode unaryCode
    (iterations rho) :=
  (ResolventSchedule.mulProgram.comp ((secondIterationFactorProgram rho).pair
    (Procedure.unarySuccessor.comp envPrecisionProgram))).congrFun (by intro e; rfl)

noncomputable opaque scheduledArgumentProgram (rho : ℕ) : Procedure scheduledInputCode
    bisectionInputCode (fun x => (iterations rho x.1, (refinedEnvironment x.1, x.2))) := by
  let e := Procedure.first environmentCode (prodCode ratCode ratCode)
  let ends := Procedure.second environmentCode (prodCode ratCode ratCode)
  exact ((iterationsProgram rho).comp e).pair
    ((refinedEnvironmentProgram.comp e).pair ends)

noncomputable opaque scheduledProgram (rho : ℕ) : Procedure scheduledInputCode ratCode
    (fun x => scheduledValue rho x.1 x.2.1 x.2.2) :=
  ((bisectionProgram rho).comp (scheduledArgumentProgram rho)).congrFun (by intro x; rfl)

noncomputable def scheduledCertificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime scheduledInputCode ratCode
      (fun x => scheduledValue rho x.1 x.2.1 x.2.2) :=
  (scheduledProgram rho).toTM2

end ContinuumCoulomb.CalibratedEvaluation

end OAI
