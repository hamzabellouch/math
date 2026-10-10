import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.TransformedGauss

namespace OAI

/-! A literal polynomial TM2 program for the transported rational Gauss
node. The reciprocal mesh denominator and lattice coordinates are binary;
the requested reciprocal error bound is unary. -/

namespace ContinuumCoulomb.TransformedGauss
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open EulerRegisters (Registers registersCode)
open RationalGaussNodes (Signs signsCode)

abbrev Input := (ℕ×ℕ)×((ℚ×ℚ)×(List (ℚ×ℚ)×(Registers×Signs)))
def inputCode : Input → List Bool :=
  prodCode (prodCode unaryCode Nat.bits)
    (prodCode (prodCode ratCode ratCode)
      (prodCode ManufacturedFieldEvaluation.sitesCode (prodCode registersCode signsCode)))

noncomputable def output (rho U C K : ℕ) (x : Input) : Triple :=
  value rho U C K x.1.1 x.1.2 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2.1 x.2.2.2.2

noncomputable opaque precisionProgram (K : ℕ) : Procedure unaryCode unaryCode (precision K) := by
  let p := Procedure.unaryMul.comp
    ((Procedure.constant unaryCode unaryCode (2*(K+1))).pair Procedure.unarySuccessor)
  exact p.congrFun (by intro P; rfl)

noncomputable opaque inputParametersProgram : Procedure inputCode (prodCode unaryCode Nat.bits) Prod.fst :=
  Procedure.first _ _
noncomputable opaque dataProgram : Procedure inputCode
    (prodCode (prodCode ratCode ratCode)
      (prodCode ManufacturedFieldEvaluation.sitesCode (prodCode registersCode signsCode))) Prod.snd :=
  Procedure.second _ _
noncomputable opaque inputPrecisionProgram (K : ℕ) : Procedure inputCode unaryCode
    (fun x => precision K x.1.1) :=
  (precisionProgram K).comp ((Procedure.first unaryCode Nat.bits).comp inputParametersProgram)
noncomputable opaque denominatorProgram : Procedure inputCode Nat.bits (fun x => x.1.2) :=
  (Procedure.second unaryCode Nat.bits).comp inputParametersProgram
noncomputable opaque fieldParametersProgram : Procedure inputCode (prodCode ratCode ratCode)
    (fun x => x.2.1) := (Procedure.first _ _).comp dataProgram
noncomputable opaque tailProgram : Procedure inputCode
    (prodCode ManufacturedFieldEvaluation.sitesCode (prodCode registersCode signsCode))
    (fun x => x.2.2) := (Procedure.second _ _).comp dataProgram
noncomputable opaque sitesProgram : Procedure inputCode ManufacturedFieldEvaluation.sitesCode
    (fun x => x.2.2.1) := (Procedure.first _ _).comp tailProgram
noncomputable opaque nodeDataProgram : Procedure inputCode (prodCode registersCode signsCode)
    (fun x => x.2.2.2) := (Procedure.second _ _).comp tailProgram

noncomputable opaque nodeArgumentsProgram (K : ℕ) : Procedure inputCode RationalGaussNodes.inputCode
    (fun x => (precision K x.1.1,(x.1.2,x.2.2.2))) :=
  (inputPrecisionProgram K).pair (denominatorProgram.pair nodeDataProgram)
noncomputable opaque initialNodeProgram (K : ℕ) : Procedure inputCode tripleCode
    (fun x => RationalGaussNodes.value (precision K x.1.1) x.1.2 x.2.2.2.1 x.2.2.2.2) :=
  RationalGaussNodes.program.comp (nodeArgumentsProgram K)
noncomputable opaque flowArgumentsProgram (K : ℕ) : Procedure inputCode ManufacturedEuler.inputCode
    (fun x => (precision K x.1.1,(x.2.1,(x.2.2.1,
      RationalGaussNodes.value (precision K x.1.1) x.1.2 x.2.2.2.1 x.2.2.2.2)))) :=
  (inputPrecisionProgram K).pair
    (fieldParametersProgram.pair (sitesProgram.pair (initialNodeProgram K)))

noncomputable opaque program (rho U C K : ℕ) : Procedure inputCode tripleCode (output rho U C K) := by
  let p := (ManufacturedEuler.program rho U C).comp (flowArgumentsProgram K)
  exact p.congrFun (by intro x; rfl)

noncomputable def certificate (rho U C K : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode tripleCode (output rho U C K) :=
  (program rho U C K).toTM2

end ContinuumCoulomb.TransformedGauss

end OAI
