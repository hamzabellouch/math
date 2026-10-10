import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedEvaluationError

namespace OAI

/-! An actual polynomial TM2 evaluator for the Coulomb-calibrated residual.
This is the numeric callback used by deterministic bisection. -/

namespace ContinuumCoulomb.CalibratedEvaluation
open ExactQuantumFactoring.BitStackProgram

attribute [local irreducible] CoulombEvaluation.approximate

def environmentCode : Environment → List Bool :=
  prodCode (prodCode unaryCode unaryCode) (prodCode unaryCode (prodCode ratCode ratCode))

def inputCode : (Environment × ℚ) → List Bool := prodCode environmentCode ratCode

noncomputable opaque coulombPrecisionProgram :
    Procedure (prodCode unaryCode unaryCode) unaryCode (fun x => coulombPrecision x.1 x.2) := by
  let n := Procedure.unarySuccessor.comp (Procedure.first unaryCode unaryCode)
  let p := ResolventSchedule.squareProgram.comp
    (Procedure.unarySuccessor.comp (Procedure.second unaryCode unaryCode))
  let prod := ResolventSchedule.mulProgram.comp (n.pair p)
  exact ((CoulombEvaluation.scaleProgram 64).comp prod).congrFun (by
    intro x
    simp only [Function.comp_apply, Nat.succ_eq_add_one, coulombPrecision]
    ring)

noncomputable opaque hoppingPrecisionProgram :
    Procedure (prodCode unaryCode unaryCode) unaryCode (fun x => hoppingPrecision x.1 x.2) := by
  let s := Procedure.unarySuccessor.comp (Procedure.first unaryCode unaryCode)
  let p := Procedure.unarySuccessor.comp (Procedure.second unaryCode unaryCode)
  let prod := ResolventSchedule.mulProgram.comp (s.pair p)
  exact ((CoulombEvaluation.scaleProgram 4).comp prod).congrFun (by
    intro x
    simp only [Function.comp_apply, Nat.succ_eq_add_one, hoppingPrecision]
    ring)

noncomputable opaque rootPrecisionProgram : Procedure unaryCode unaryCode rootPrecision :=
  ((CoulombEvaluation.scaleProgram 8).comp Procedure.unarySuccessor).congrFun (by intro x; rfl)

noncomputable opaque environmentProgram : Procedure inputCode environmentCode Prod.fst :=
  Procedure.first environmentCode ratCode
noncomputable opaque distanceProgram : Procedure inputCode ratCode Prod.snd :=
  Procedure.second environmentCode ratCode
noncomputable opaque metadataProgram : Procedure inputCode (prodCode unaryCode unaryCode)
    (fun x => x.1.1) :=
  (Procedure.first (prodCode unaryCode unaryCode)
    (prodCode unaryCode (prodCode ratCode ratCode))).comp environmentProgram
noncomputable opaque boundProgram : Procedure inputCode unaryCode (fun x => x.1.1.1) :=
  (Procedure.first unaryCode unaryCode).comp metadataProgram
noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.1.2) :=
  (Procedure.second unaryCode unaryCode).comp metadataProgram
noncomputable opaque parametersProgram : Procedure inputCode
    (prodCode unaryCode (prodCode ratCode ratCode)) (fun x => x.1.2) :=
  (Procedure.second (prodCode unaryCode unaryCode)
    (prodCode unaryCode (prodCode ratCode ratCode))).comp environmentProgram
noncomputable opaque scaleProgram : Procedure inputCode unaryCode (fun x => x.1.2.1) :=
  (Procedure.first unaryCode (prodCode ratCode ratCode)).comp parametersProgram
noncomputable opaque scalarParametersProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.1.2.2) :=
  (Procedure.second unaryCode (prodCode ratCode ratCode)).comp parametersProgram
noncomputable opaque tauProgram : Procedure inputCode ratCode (fun x => x.1.2.2.1) :=
  (Procedure.first ratCode ratCode).comp scalarParametersProgram
noncomputable opaque weightProgram : Procedure inputCode ratCode (fun x => x.1.2.2.2) :=
  (Procedure.second ratCode ratCode).comp scalarParametersProgram
noncomputable opaque coulombAccuracyProgram : Procedure inputCode unaryCode
    (fun x => coulombPrecision x.1.1.1 x.1.1.2) :=
  coulombPrecisionProgram.comp metadataProgram
noncomputable def onsiteArgument (x : Environment × ℚ) : CoulombEvaluation.Input :=
  (coulombPrecision x.1.1.1 x.1.1.2, 0)
noncomputable def separatedArgument (x : Environment × ℚ) : CoulombEvaluation.Input :=
  (coulombPrecision x.1.1.1 x.1.1.2, x.2)

noncomputable opaque onsiteArgumentProgram :
    Procedure inputCode CoulombEvaluation.inputCode onsiteArgument :=
  coulombAccuracyProgram.pair (Procedure.constant inputCode ratCode 0)
noncomputable opaque separatedArgumentProgram :
    Procedure inputCode CoulombEvaluation.inputCode separatedArgument :=
  coulombAccuracyProgram.pair distanceProgram

noncomputable opaque onsiteRawProgram (rho : ℕ) : Procedure inputCode ratCode
    ((fun q : CoulombEvaluation.Input => CoulombEvaluation.approximate rho q.1 q.2) ∘ onsiteArgument) :=
  (CoulombEvaluation.program rho).comp onsiteArgumentProgram
noncomputable opaque separatedRawProgram (rho : ℕ) : Procedure inputCode ratCode
    ((fun q : CoulombEvaluation.Input => CoulombEvaluation.approximate rho q.1 q.2) ∘ separatedArgument) :=
  (CoulombEvaluation.program rho).comp separatedArgumentProgram

noncomputable opaque onsiteProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => CoulombEvaluation.approximate rho (coulombPrecision x.1.1.1 x.1.1.2) 0) :=
  (onsiteRawProgram rho).congrFun (by intro x; simp only [Function.comp_apply, onsiteArgument])
noncomputable opaque separatedProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => CoulombEvaluation.approximate rho (coulombPrecision x.1.1.1 x.1.1.2) x.2) :=
  (separatedRawProgram rho).congrFun (by intro x; simp only [Function.comp_apply, separatedArgument])

noncomputable opaque gapProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => gap rho x.1.1.1 x.1.1.2 x.2) :=
  (CappedKernelProgram.maximumProgram.comp ((Procedure.constant inputCode ratCode 0).pair
    (Procedure.ratSub.comp ((onsiteProgram rho).pair (separatedProgram rho))))).congrFun
      (by intro x; rfl)
noncomputable opaque radicandProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => x.1.2.2.2 * gap rho x.1.1.1 x.1.1.2 x.2) :=
  Procedure.ratMul.comp (weightProgram.pair (gapProgram rho))
noncomputable opaque rootProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2) :=
  (RationalSquareRoot.program.comp
    ((rootPrecisionProgram.comp precisionProgram).pair (radicandProgram rho))).congrFun
      (by intro x; rfl)
noncomputable opaque hoppingAccuracyProgram : Procedure inputCode unaryCode
    (fun x => hoppingPrecision x.1.2.1 x.1.1.2) :=
  hoppingPrecisionProgram.comp (scaleProgram.pair precisionProgram)
noncomputable opaque hoppingProgram : Procedure inputCode ratCode
    (fun x => ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2)) :=
  ComputableHopping.program.comp ((boundProgram.pair hoppingAccuracyProgram).pair distanceProgram)
noncomputable opaque scaledHoppingProgram : Procedure inputCode ratCode
    (fun x => (x.1.2.1 : ℚ) *
      ComputableHopping.approximate ((x.1.1.1, hoppingPrecision x.1.2.1 x.1.1.2), x.2)) :=
  Procedure.ratMul.comp ((Procedure.natToRat.comp
    (Procedure.unaryToBits.comp scaleProgram)).pair hoppingProgram)
noncomputable opaque targetProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => x.1.2.2.1 * root rho x.1.1.1 x.1.1.2 x.1.2.2.2 x.2) :=
  Procedure.ratMul.comp (tauProgram.pair (rootProgram rho))

end ContinuumCoulomb.CalibratedEvaluation

end OAI
