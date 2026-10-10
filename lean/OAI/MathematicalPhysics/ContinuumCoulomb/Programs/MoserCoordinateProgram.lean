import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedEuler
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ManufacturedVelocityProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.EulerProgram

namespace OAI

/-! A deterministic polynomial TM2 program for the actual rounded Moser
coordinate construction. The fixed integers U,C occur as hardcoded constants;
precision is unary and geometric input data are binary rationals. -/

namespace ContinuumCoulomb.ManufacturedEuler
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)
open EulerRegisters

abbrev Input := ManufacturedFieldEvaluation.Input
def inputCode : Input → List Bool := ManufacturedFieldEvaluation.inputCode

noncomputable def value (rho U C : ℕ) (x : Input) : Triple :=
  approximate rho U C x.1 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2

noncomputable opaque stepsProgram (C : ℕ) : Procedure unaryCode unaryCode (steps C) :=
  Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode (16*C^2)).pair Procedure.unarySuccessor)
noncomputable opaque inputStepsProgram (C : ℕ) : Procedure inputCode unaryCode (fun x => steps C x.1) :=
  (stepsProgram C).comp (Procedure.first unaryCode
    (prodCode (prodCode ratCode ratCode) (prodCode ManufacturedFieldEvaluation.sitesCode tripleCode)))
noncomputable opaque denominatorProgram (C : ℕ) : Procedure inputCode Nat.bits (fun x => denominator C x.1) := by
  let n := Procedure.unaryToBits.comp (inputStepsProgram C)
  exact (Procedure.binaryMul.comp (n.pair n)).congrFun (by intro x; simp only [denominator,pow_two]; rfl)
noncomputable opaque inputPointProgram : Procedure inputCode tripleCode (fun x => x.2.2.2) :=
  ManufacturedFieldEvaluation.pointProgram

noncomputable opaque inputRadiusProgram : Procedure tripleCode Nat.bits inputRadius := by
  let a := Procedure.intAbs.comp (Procedure.ratNum.comp tripleFirstProgram)
  let b := Procedure.intAbs.comp (Procedure.ratNum.comp tripleSecondProgram)
  let c := Procedure.intAbs.comp (Procedure.ratNum.comp tripleThirdProgram)
  exact Procedure.binaryAdd.comp ((Procedure.binaryAdd.comp (a.pair b)).pair c)
noncomputable opaque boxProgram (U C : ℕ) : Procedure inputCode Nat.bits
    (fun x => boxNumerator U (denominator C x.1) x.2.2.2) := by
  let r := inputRadiusProgram.comp inputPointProgram
  let u := Procedure.constant inputCode Nat.bits U
  let r' := Procedure.successor.comp (Procedure.binaryAdd.comp (r.pair u))
  exact (Procedure.binaryMul.comp ((denominatorProgram C).pair r')).congrFun (by intro x; rfl)
noncomputable opaque stepProgram (C : ℕ) : Procedure inputCode ratCode
    (fun x => (steps C x.1:ℚ)⁻¹) :=
  Procedure.ratInv.comp (Procedure.natToRat.comp (Procedure.unaryToBits.comp (inputStepsProgram C)))

noncomputable opaque environmentProgram (C : ℕ) :
    Procedure inputCode ManufacturedVelocityEvaluation.environmentCode
      (fun x => (steps C x.1,(x.2.1,x.2.2.1))) :=
  (inputStepsProgram C).pair
    (ManufacturedFieldEvaluation.parametersProgram.pair ManufacturedFieldEvaluation.sitesProgram)
noncomputable opaque parameterNumbersProgram (U C : ℕ) :
    Procedure inputCode (prodCode Nat.bits (prodCode Nat.bits ratCode))
      (fun x => (denominator C x.1,(boxNumerator U (denominator C x.1) x.2.2.2,(steps C x.1:ℚ)⁻¹))) :=
  (denominatorProgram C).pair ((boxProgram U C).pair (stepProgram C))
noncomputable opaque parametersProgram (U C : ℕ) :
    Procedure inputCode (parametersCode ManufacturedVelocityEvaluation.environmentCode)
      (fun x => ((steps C x.1,(x.2.1,x.2.2.1)),
        (denominator C x.1,(boxNumerator U (denominator C x.1) x.2.2.2,(steps C x.1:ℚ)⁻¹)))) :=
  (environmentProgram C).pair (parameterNumbersProgram U C)
noncomputable opaque registersProgram (U C : ℕ) : Procedure inputCode registersCode
    (fun x => round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2) :=
  by
    let p := roundProgram.comp (((denominatorProgram C).pair (boxProgram U C)).pair inputPointProgram)
    exact p.congrFun (by intro x; rfl)
noncomputable opaque initialProgram (U C : ℕ) :
    Procedure inputCode (configCode ManufacturedVelocityEvaluation.environmentCode)
      (fun x => initial (steps C x.1,(x.2.1,x.2.2.1)) (steps C x.1) (denominator C x.1)
        (boxNumerator U (denominator C x.1) x.2.2.2)
        (round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2)) :=
  (parametersProgram U C).pair
    ((Procedure.constant inputCode Nat.bits 0).pair (registersProgram U C))
noncomputable opaque runArgumentsProgram (U C : ℕ) :
    Procedure inputCode (prodCode unaryCode (configCode ManufacturedVelocityEvaluation.environmentCode))
      (fun x => (steps C x.1, initial (steps C x.1,(x.2.1,x.2.2.1)) (steps C x.1)
        (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2)
        (round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2))) :=
  (inputStepsProgram C).pair (initialProgram U C)

private theorem run_initial (rho : ℕ) (e : Environment) (N D B : ℕ) (r : Registers) :
    run (evaluate rho) (N,initial e N D B r) = trajectory (evaluate rho) e N D B r N := by
  change point (((advance (evaluate rho))^[N] (initial e N D B r)).1.2.1)
    (((advance (evaluate rho))^[N] (initial e N D B r)).2.2) = _
  rw [iterate_parameters]
  rfl

noncomputable opaque program (rho U C : ℕ) : Procedure inputCode tripleCode (value rho U C) := by
  let p := (EulerRegisters.program (E := Environment)
    (ce := ManufacturedVelocityEvaluation.environmentCode) (evaluate := evaluate rho)
    (ManufacturedVelocityEvaluation.program rho)).comp
    (runArgumentsProgram U C)
  exact p.congrFun (by
    intro x
    change run (evaluate rho) (steps C x.1,initial (steps C x.1,(x.2.1,x.2.2.1))
      (steps C x.1) (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2)
      (round (denominator C x.1) (boxNumerator U (denominator C x.1) x.2.2.2) x.2.2.2)) = _
    rw [run_initial]
    rfl)

noncomputable def certificate (rho U C : ℕ) :
    Turing.TM2ComputableInPolyTime inputCode tripleCode (value rho U C) := (program rho U C).toTM2

end ContinuumCoulomb.ManufacturedEuler

end OAI
