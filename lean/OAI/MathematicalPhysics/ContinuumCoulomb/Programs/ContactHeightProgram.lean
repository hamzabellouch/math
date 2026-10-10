import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactHeightEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibratedEvaluationComponents
import OAI.Computability.QuantumFactoring.BitStackListIndex

namespace OAI

/-! A literal rational height-residual program. It reads nine input lengths
and executes four already-certified rational square-root subprograms. -/

namespace ContinuumCoulomb.ContactHeightEvaluation
open ExactQuantumFactoring.BitStackProgram

def environmentCode : Environment → List Bool :=
  prodCode unaryCode (prodCode (listCode ratCode) ratCode)

def inputCode : (Environment × ℚ) → List Bool := prodCode environmentCode ratCode

noncomputable opaque environmentProgram : Procedure inputCode environmentCode Prod.fst :=
  Procedure.first environmentCode ratCode

noncomputable opaque heightProgram : Procedure inputCode ratCode Prod.snd :=
  Procedure.second environmentCode ratCode

noncomputable opaque precisionProgram : Procedure inputCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode (prodCode (listCode ratCode) ratCode)).comp environmentProgram

noncomputable opaque dataProgram : Procedure inputCode (prodCode (listCode ratCode) ratCode)
    (fun x => x.1.2) :=
  (Procedure.second unaryCode (prodCode (listCode ratCode) ratCode)).comp environmentProgram

noncomputable opaque lengthsProgram : Procedure inputCode (listCode ratCode)
    (fun x => x.1.2.1) :=
  (Procedure.first (listCode ratCode) ratCode).comp dataProgram

noncomputable opaque targetProgram : Procedure inputCode ratCode (fun x => x.1.2.2) :=
  (Procedure.second (listCode ratCode) ratCode).comp dataProgram

noncomputable opaque lengthProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => lengthAt x.1 k) :=
  (Procedure.listGet ratCode 1).comp
    ((Procedure.constant inputCode Nat.bits k).pair lengthsProgram)

noncomputable opaque squareLengthProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => (lengthAt x.1 k) ^ 2) :=
  (Procedure.ratMul.comp ((lengthProgram k).pair (lengthProgram k))).congrFun
    (by intro x; simp only [Function.comp_apply, pow_two])

noncomputable opaque squareHeightProgram : Procedure inputCode ratCode
    (fun x => x.2 ^ 2) :=
  (Procedure.ratMul.comp (heightProgram.pair heightProgram)).congrFun
    (by intro x; simp only [Function.comp_apply, pow_two])

noncomputable opaque radicandProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => (lengthAt x.1 k) ^ 2 - x.2 ^ 2) :=
  Procedure.ratSub.comp ((squareLengthProgram k).pair squareHeightProgram)

noncomputable opaque rootPrecisionProgram : Procedure inputCode unaryCode
    (fun x => CalibratedEvaluation.rootPrecision x.1.1) :=
  CalibratedEvaluation.rootPrecisionProgram.comp precisionProgram

noncomputable opaque rootProgram (k : ℕ) : Procedure inputCode ratCode
    (fun x => rootSample x.1 x.2 k) :=
  RationalSquareRoot.program.comp (rootPrecisionProgram.pair (radicandProgram k))

noncomputable opaque axial01Program : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1) :=
  Procedure.ratAdd.comp ((lengthProgram 0).pair (lengthProgram 1))

noncomputable opaque axial014Program : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4) :=
  Procedure.ratAdd.comp (axial01Program.pair (lengthProgram 4))

noncomputable opaque axial0147Program : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7) :=
  Procedure.ratAdd.comp (axial014Program.pair (lengthProgram 7))

noncomputable opaque axialProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8) :=
  Procedure.ratAdd.comp (axial0147Program.pair (lengthProgram 8))

noncomputable opaque firstRootProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2) := Procedure.ratAdd.comp (axialProgram.pair (rootProgram 2))

noncomputable opaque secondRootProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2 + rootSample x.1 x.2 3) :=
  Procedure.ratAdd.comp (firstRootProgram.pair (rootProgram 3))

noncomputable opaque thirdRootProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2 + rootSample x.1 x.2 3 + rootSample x.1 x.2 5) :=
  Procedure.ratAdd.comp (secondRootProgram.pair (rootProgram 5))

noncomputable opaque spanProgram : Procedure inputCode ratCode
    (fun x => lengthAt x.1 0 + lengthAt x.1 1 + lengthAt x.1 4 + lengthAt x.1 7 + lengthAt x.1 8 +
      rootSample x.1 x.2 2 + rootSample x.1 x.2 3 + rootSample x.1 x.2 5 + rootSample x.1 x.2 6) :=
  Procedure.ratAdd.comp (thirdRootProgram.pair (rootProgram 6))

noncomputable opaque program : Procedure inputCode ratCode (fun x => value x.1 x.2) :=
  Procedure.ratSub.comp (spanProgram.pair targetProgram)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode ratCode
    (fun x => value x.1 x.2) := program.toTM2

end ContinuumCoulomb.ContactHeightEvaluation

end OAI
