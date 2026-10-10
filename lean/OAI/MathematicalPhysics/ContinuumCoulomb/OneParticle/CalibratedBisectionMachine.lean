import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedBisection
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CalibratedEvaluationProgram

namespace OAI

/-! Literal bisection with the certified calibrated-residual machine. -/

noncomputable section
namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque bisectionProgram (rho : ℕ) : Procedure bisectionInputCode ratCode (bisect rho) :=
  ((BisectionProgram.program (program rho)).comp bisectionArgumentProgram).congrFun
    (by intro x; rfl)

noncomputable def bisectionCertificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime bisectionInputCode ratCode (bisect rho) :=
  (bisectionProgram rho).toTM2


end ContinuumCoulomb.CalibratedEvaluation

end

end OAI
