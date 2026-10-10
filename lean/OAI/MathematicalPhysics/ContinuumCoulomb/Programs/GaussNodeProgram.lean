import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalGaussNodes
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.EulerVectorPrograms

namespace OAI

/-! Literal polynomial-time generation of an initial rational tensor-Gauss
node. Integer lattice coordinates and the reciprocal mesh denominator are
binary; the approximation precision is unary. -/

namespace ContinuumCoulomb.RationalGaussNodes
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open EulerRegisters (registersCode)

def signsCode : Signs → List Bool := prodCode Procedure.boolCode
  (prodCode Procedure.boolCode Procedure.boolCode)
abbrev Input := ℕ×(ℕ×(EulerRegisters.Registers×Signs))
def inputCode : Input → List Bool := prodCode unaryCode (prodCode Nat.bits (prodCode registersCode signsCode))

noncomputable opaque precisionProgram : Procedure unaryCode unaryCode (fun P => 2*(P+1)) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode 2).pair Procedure.unarySuccessor)
noncomputable opaque abscissaProgram : Procedure unaryCode ratCode abscissa := by
  let p := RationalSquareRoot.program.comp (precisionProgram.pair
    (Procedure.constant unaryCode ratCode (1/3:ℚ)))
  exact p.congrFun (by intro P; rfl)
noncomputable opaque signedProgram : Procedure (prodCode unaryCode Procedure.boolCode) ratCode
    (fun x => signed x.1 x.2) := by
  let p := abscissaProgram.comp (Procedure.first unaryCode Procedure.boolCode)
  let b := Procedure.second unaryCode Procedure.boolCode
  exact (Procedure.conditional b p (Procedure.ratNeg.comp p)).congrFun (by
    intro x
    cases h : x.2 <;> simp only [Function.comp_apply,Bool.false_eq_true,ite_false,ite_true,signed])

abbrev CoordinateInput := (ℕ×ℕ)×(ℤ×Bool)
def coordinateCode : CoordinateInput → List Bool := prodCode (prodCode unaryCode Nat.bits)
  (prodCode intCode Procedure.boolCode)
noncomputable opaque coordinateParametersProgram : Procedure coordinateCode (prodCode unaryCode Nat.bits) Prod.fst :=
  Procedure.first _ _
noncomputable opaque coordinateDataProgram : Procedure coordinateCode (prodCode intCode Procedure.boolCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque coordinatePrecisionProgram : Procedure coordinateCode unaryCode (fun x => x.1.1) :=
  (Procedure.first unaryCode Nat.bits).comp coordinateParametersProgram
noncomputable opaque coordinateDenominatorProgram : Procedure coordinateCode ratCode (fun x => (x.1.2:ℚ)) :=
  Procedure.natToRat.comp ((Procedure.second unaryCode Nat.bits).comp coordinateParametersProgram)
noncomputable opaque coordinateIntegerProgram : Procedure coordinateCode ratCode (fun x => (x.2.1:ℚ)) :=
  Procedure.intToRat.comp ((Procedure.first intCode Procedure.boolCode).comp coordinateDataProgram)
noncomputable opaque coordinateSignProgram : Procedure coordinateCode Procedure.boolCode (fun x => x.2.2) :=
  (Procedure.second intCode Procedure.boolCode).comp coordinateDataProgram
noncomputable opaque coordinateHalfProgram : Procedure coordinateCode ratCode
    (fun x => signed x.1.1 x.2.2/2) :=
  Procedure.ratDiv.comp ((signedProgram.comp (coordinatePrecisionProgram.pair coordinateSignProgram)).pair
    (Procedure.constant coordinateCode ratCode (2:ℚ)))
noncomputable opaque coordinateProgram : Procedure coordinateCode ratCode
    (fun x => ((x.2.1:ℚ)+signed x.1.1 x.2.2/2)/x.1.2) :=
  Procedure.ratDiv.comp ((Procedure.ratAdd.comp (coordinateIntegerProgram.pair coordinateHalfProgram)).pair
    coordinateDenominatorProgram)

noncomputable opaque dataProgram : Procedure inputCode (prodCode Nat.bits (prodCode registersCode signsCode)) Prod.snd :=
  Procedure.second unaryCode _
noncomputable opaque parametersProgram : Procedure inputCode (prodCode unaryCode Nat.bits)
    (fun x => (x.1,x.2.1)) :=
  (Procedure.first unaryCode _).pair ((Procedure.first Nat.bits _).comp dataProgram)
noncomputable opaque nodeDataProgram : Procedure inputCode (prodCode registersCode signsCode)
    (fun x => x.2.2) := (Procedure.second Nat.bits _).comp dataProgram
noncomputable opaque registersProgram : Procedure inputCode registersCode (fun x => x.2.2.1) :=
  (Procedure.first registersCode signsCode).comp nodeDataProgram
noncomputable opaque signsProgram : Procedure inputCode signsCode (fun x => x.2.2.2) :=
  (Procedure.second registersCode signsCode).comp nodeDataProgram
noncomputable opaque signFirstProgram : Procedure signsCode Procedure.boolCode Prod.fst := Procedure.first _ _
noncomputable opaque signTailProgram : Procedure signsCode (prodCode Procedure.boolCode Procedure.boolCode) Prod.snd :=
  Procedure.second _ _
noncomputable opaque signSecondProgram : Procedure signsCode Procedure.boolCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp signTailProgram
noncomputable opaque signThirdProgram : Procedure signsCode Procedure.boolCode (fun x => x.2.2) :=
  (Procedure.second _ _).comp signTailProgram

noncomputable opaque program : Procedure inputCode tripleCode
    (fun x => value x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let a := coordinateProgram.comp (parametersProgram.pair
    ((EulerRegisters.firstRegisterProgram.comp registersProgram).pair (signFirstProgram.comp signsProgram)))
  let b := coordinateProgram.comp (parametersProgram.pair
    ((EulerRegisters.secondRegisterProgram.comp registersProgram).pair (signSecondProgram.comp signsProgram)))
  let c := coordinateProgram.comp (parametersProgram.pair
    ((EulerRegisters.thirdRegisterProgram.comp registersProgram).pair (signThirdProgram.comp signsProgram)))
  exact a.pair (b.pair c)

noncomputable def certificate : Turing.TM2ComputableInPolyTime inputCode tripleCode
    (fun x => value x.1 x.2.1 x.2.2.1 x.2.2.2) := program.toTM2

end ContinuumCoulomb.RationalGaussNodes

end OAI
