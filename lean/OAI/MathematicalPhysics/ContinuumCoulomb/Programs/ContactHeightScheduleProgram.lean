import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactHeightBisection
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactHeightProgram

namespace OAI

/-! Polynomial-time execution of the concrete contact-height search. All
precision and iteration counts are unary linear functions of the request. -/

namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque envPrecisionProgram : Procedure environmentCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode (listCode ratCode) ratCode)

noncomputable opaque envDataProgram : Procedure environmentCode
    (prodCode (listCode ratCode) ratCode) Prod.snd :=
  Procedure.second unaryCode (prodCode (listCode ratCode) ratCode)

noncomputable opaque refinedPrecisionProgram : Procedure environmentCode unaryCode
    (fun e => 16 * (e.1 + 1)) :=
  ((CoulombEvaluation.scaleProgram 16).comp Procedure.unarySuccessor).comp envPrecisionProgram

noncomputable opaque refinedProgram : Procedure environmentCode environmentCode
    refinedEnvironment := refinedPrecisionProgram.pair envDataProgram

noncomputable opaque iterationProgram : Procedure environmentCode unaryCode iterations :=
  ((CoulombEvaluation.scaleProgram 64).comp Procedure.unarySuccessor).comp envPrecisionProgram

noncomputable opaque toleranceProgram : Procedure environmentCode ratCode
    (fun e => tolerance (refinedEnvironment e)) := by
  let successor := Procedure.unarySuccessor.comp refinedPrecisionProgram
  let rational := Procedure.natToRat.comp (Procedure.unaryToBits.comp successor)
  exact (Procedure.ratInv.comp rational).congrFun (by
    intro e
    simp only [Function.comp_apply, id_eq, tolerance, refinedEnvironment,
      Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div])

noncomputable opaque scheduledArgumentProgram : Procedure environmentCode
    (BisectionProgram.inputCode environmentCode)
    (fun e => argument (refinedEnvironment e) (iterations e)) :=
  iterationProgram.pair (refinedProgram.pair
    (toleranceProgram.pair (Procedure.constant environmentCode
      (prodCode ratCode ratCode) ((2 / 5 : ℚ), (3 / 4 : ℚ)))))

noncomputable opaque scheduledProgram : Procedure environmentCode ratCode scheduledValue :=
  ((BisectionProgram.program program).comp scheduledArgumentProgram).congrFun
    (by intro e; rfl)

noncomputable def scheduledCertificate : Turing.TM2ComputableInPolyTime
    environmentCode ratCode scheduledValue := scheduledProgram.toTM2

end ContinuumCoulomb.ContactHeightEvaluation

end OAI
