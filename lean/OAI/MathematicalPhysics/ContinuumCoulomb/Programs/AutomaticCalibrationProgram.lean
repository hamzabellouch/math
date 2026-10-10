import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.AutomaticCalibrationParameters

namespace OAI

/-! The automatic distance program computes its polynomial query bounds,
scale and inverse-power target from unary source size, then runs the
certified rational-interval calibrated bisection. -/

namespace ContinuumCoulomb.AutomaticCalibration
open ExactQuantumFactoring.BitStackProgram

def inputCode : Input → List Bool := prodCode unaryCode (prodCode unaryCode ratCode)

noncomputable def unaryPowerProgram : (k : ℕ) → Procedure unaryCode unaryCode (fun n => n ^ k)
  | 0 => Procedure.constant unaryCode unaryCode 1
  | k + 1 => (ResolventSchedule.mulProgram.comp
      ((unaryPowerProgram k).pair (Procedure.identity unaryCode))).congrFun
        (by intro n; simp only [Function.comp_apply, id_eq, pow_succ])

noncomputable opaque baseProgram : Procedure inputCode unaryCode Prod.fst :=
  Procedure.first unaryCode (prodCode unaryCode ratCode)

noncomputable opaque tailProgram : Procedure inputCode (prodCode unaryCode ratCode) Prod.snd :=
  Procedure.second unaryCode (prodCode unaryCode ratCode)

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first unaryCode ratCode).comp tailProgram

noncomputable opaque coefficientProgram : Procedure inputCode ratCode (fun x => x.2.2) :=
  (Procedure.second unaryCode ratCode).comp tailProgram

noncomputable opaque scaledSizeProgram (k : ℕ) : Procedure inputCode unaryCode
    (fun x => 2 * k * x.1) := (CoulombEvaluation.scaleProgram (2 * k)).comp baseProgram

noncomputable opaque queryProgram (k A : ℕ) : Procedure inputCode unaryCode
    (fun x => queryBound k A x.1) :=
  Procedure.unarySuccessor.comp (ResolventSchedule.addProgram.comp
    ((scaledSizeProgram k).pair ((unaryPowerProgram A).comp baseProgram)))

noncomputable opaque scaleProgram (k : ℕ) : Procedure inputCode unaryCode
    (fun x => x.1 ^ k) := (unaryPowerProgram k).comp baseProgram

noncomputable opaque targetScaleProgram (B : ℕ) : Procedure inputCode ratCode
    (fun x => ((x.1 ^ B : ℕ) : ℚ)⁻¹) :=
  Procedure.ratInv.comp (Procedure.natToRat.comp
    (Procedure.unaryToBits.comp ((unaryPowerProgram B).comp baseProgram)))

noncomputable opaque environmentProgram (k A B : ℕ) : Procedure inputCode
    CalibratedEvaluation.environmentCode (environment k A B) :=
  ((queryProgram k A).pair precisionProgram).pair
    ((scaleProgram k).pair ((targetScaleProgram B).pair coefficientProgram))

noncomputable opaque intervalProgram (ε c : ℚ) (k : ℕ) : Procedure inputCode
    (prodCode ratCode ratCode) (fun x => interval ε c k x.1) :=
  (CalibrationRationalBracket.program ε c k).comp baseProgram

noncomputable opaque argumentProgram (ε c : ℚ) (k A B : ℕ) : Procedure inputCode
    CalibratedEvaluation.scheduledInputCode
      (fun x => (environment k A B x, interval ε c k x.1)) :=
  (environmentProgram k A B).pair (intervalProgram ε c k)

noncomputable opaque program (rho : ℕ) (ε c : ℚ) (k A B : ℕ) : Procedure inputCode ratCode
    (value rho ε c k A B) :=
  ((CalibratedEvaluation.scheduledProgram rho).comp (argumentProgram ε c k A B)).congrFun
    (by intro x; rfl)

noncomputable def certificate (rho : ℕ) (ε c : ℚ) (k A B : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode ratCode (value rho ε c k A B) :=
  (program rho ε c k A B).toTM2

end ContinuumCoulomb.AutomaticCalibration

end OAI
