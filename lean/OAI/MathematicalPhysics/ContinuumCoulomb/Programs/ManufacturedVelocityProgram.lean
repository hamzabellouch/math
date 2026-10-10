import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedVelocityEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ManufacturedFieldProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MoserDifferenceProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.FiniteDifferenceProgram

namespace OAI

/-! The manufactured Moser velocity has a literal polynomial TM2 evaluator.
It composes the already certified field sampler, three fixed rational
coordinate differences, and the clamped positive-density quotient. -/

namespace ContinuumCoulomb.ManufacturedVelocityEvaluation
open ExactQuantumFactoring.BitStackProgram
open CappedKernelProgram (Triple tripleCode)

abbrev Environment := ℕ×((ℚ×ℚ)×List (ℚ×ℚ))
def environmentCode : Environment → List Bool := prodCode unaryCode
  (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode)
def sampleCode : (Environment×Triple) → List Bool := prodCode environmentCode tripleCode
abbrev Input := Environment×(ℚ×Triple)
def inputCode : Input → List Bool := prodCode environmentCode (prodCode ratCode tripleCode)

noncomputable opaque envPrecisionProgram : Procedure environmentCode unaryCode Prod.fst :=
  Procedure.first unaryCode _
noncomputable opaque envDataProgram : Procedure environmentCode
    (prodCode (prodCode ratCode ratCode) ManufacturedFieldEvaluation.sitesCode) Prod.snd :=
  Procedure.second unaryCode _
noncomputable opaque envParametersProgram : Procedure environmentCode (prodCode ratCode ratCode)
    (fun e => e.2.1) := (Procedure.first _ _).comp envDataProgram
noncomputable opaque envSitesProgram : Procedure environmentCode ManufacturedFieldEvaluation.sitesCode
    (fun e => e.2.2) := (Procedure.second _ _).comp envDataProgram
noncomputable opaque innerPrecisionProgram (rho : ℕ) : Procedure unaryCode unaryCode (precision rho) :=
  (Procedure.unaryMul.comp ((Procedure.constant unaryCode unaryCode
    (12*(1+MoserDifferenceBudget.guard*(4*rho+1)))).pair Procedure.unarySuccessor))

noncomputable opaque sampleEnvironmentProgram : Procedure sampleCode environmentCode Prod.fst :=
  Procedure.first environmentCode tripleCode
noncomputable opaque samplePointProgram : Procedure sampleCode tripleCode Prod.snd :=
  Procedure.second environmentCode tripleCode
noncomputable opaque samplePrecisionProgram : Procedure sampleCode unaryCode
    (fun x => MoserDifferenceBudget.precision x.1.1) :=
  MoserDifferenceBudget.precisionProgram.comp (envPrecisionProgram.comp sampleEnvironmentProgram)
noncomputable opaque sampleDataProgram : Procedure sampleCode
    (prodCode (prodCode ratCode ratCode) (prodCode ManufacturedFieldEvaluation.sitesCode tripleCode))
    (fun x => (x.1.2.1,(x.1.2.2,x.2))) :=
  (envParametersProgram.comp sampleEnvironmentProgram).pair
    ((envSitesProgram.comp sampleEnvironmentProgram).pair samplePointProgram)
noncomputable opaque scalarSampleProgram (rho : ℕ) : Procedure sampleCode ratCode
    (fun x => sample rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2) :=
  by
    let p := (ManufacturedFieldEvaluation.program rho).comp (samplePrecisionProgram.pair sampleDataProgram)
    exact p.congrFun (by intro x; rfl)
noncomputable opaque spatialStepProgram : Procedure environmentCode ratCode
    (fun e => MoserDifferenceBudget.step e.1) :=
  MoserDifferenceBudget.stepProgram.comp envPrecisionProgram

noncomputable opaque gradientProgram (rho : ℕ) (a : Fin 3) : Procedure sampleCode ratCode
    (fun x => gradient rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2 a) :=
  by
    let p := FiniteDifferenceProgram.firstProgram (E := Environment) (ce := environmentCode)
      (sample := fun e q => sample rho e.1 e.2.1.1 e.2.1.2 e.2.2 q)
      (step := fun e => MoserDifferenceBudget.step e.1) a (scalarSampleProgram rho) spatialStepProgram
    exact p.congrFun (by intro x; rfl)
noncomputable opaque laplacianProgram (rho : ℕ) : Procedure sampleCode ratCode
    (fun x => laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2) :=
  by
    let p := FiniteDifferenceProgram.laplacianProgram (E := Environment) (ce := environmentCode)
      (sample := fun e q => sample rho e.1 e.2.1.1 e.2.1.2 e.2.2 q)
      (step := fun e => MoserDifferenceBudget.step e.1) (scalarSampleProgram rho) spatialStepProgram
    exact p.congrFun (by intro x; rfl)
noncomputable opaque piProgram : Procedure environmentCode ratCode (fun e => pi e.1) :=
  PiProgram.program.comp ((Procedure.unaryMul.comp
    ((Procedure.constant unaryCode unaryCode 8).pair Procedure.unarySuccessor)).comp envPrecisionProgram)

noncomputable opaque inputEnvironmentProgram : Procedure inputCode environmentCode Prod.fst :=
  Procedure.first environmentCode (prodCode ratCode tripleCode)
noncomputable opaque inputTimePointProgram : Procedure inputCode (prodCode ratCode tripleCode) Prod.snd :=
  Procedure.second environmentCode (prodCode ratCode tripleCode)
noncomputable opaque inputTimeProgram : Procedure inputCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode tripleCode).comp inputTimePointProgram
noncomputable opaque inputPointProgram : Procedure inputCode tripleCode (fun x => x.2.2) :=
  (Procedure.second ratCode tripleCode).comp inputTimePointProgram
noncomputable opaque inputSampleProgram : Procedure inputCode sampleCode (fun x => (x.1,x.2.2)) :=
  inputEnvironmentProgram.pair inputPointProgram
noncomputable opaque rawDenominatorProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => 4*pi x.1.1*(rho:ℚ)+x.2.1*laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2) := by
  let base := Procedure.ratMul.comp ((Procedure.constant inputCode ratCode (4:ℚ)).pair
    (piProgram.comp inputEnvironmentProgram))
  let first := Procedure.ratMul.comp (base.pair (Procedure.constant inputCode ratCode (rho:ℚ)))
  let second := Procedure.ratMul.comp (inputTimeProgram.pair ((laplacianProgram rho).comp inputSampleProgram))
  exact Procedure.ratAdd.comp (first.pair second)

noncomputable opaque maxDensityProgram (rho : ℕ) : Procedure ratCode ratCode (fun q => max (rho:ℚ) q) := by
  let q := Procedure.identity ratCode
  let r := Procedure.constant ratCode ratCode (rho:ℚ)
  let negative := Procedure.intSign.comp (Procedure.ratNum.comp (Procedure.ratSub.comp (q.pair r)))
  exact (Procedure.conditional negative r q).congrFun (by
    intro q
    simp only [Function.comp_apply,Rat.num_neg,decide_eq_true_eq,id_eq]
    split_ifs with h
    · exact (max_eq_left (by linarith)).symm
    · exact (max_eq_right (by linarith)).symm)

noncomputable opaque denominatorProgram (rho : ℕ) : Procedure inputCode ratCode
    (fun x => max (rho:ℚ) (4*pi x.1.1*(rho:ℚ)+x.2.1*
      laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2)) :=
  (maxDensityProgram rho).comp (rawDenominatorProgram rho)
noncomputable opaque coreComponentProgram (rho : ℕ) (a : Fin 3) : Procedure inputCode ratCode
    (fun x => -gradient rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2 a /
      max (rho:ℚ) (4*pi x.1.1*(rho:ℚ)+x.2.1*
        laplacian rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.2)) :=
  Procedure.ratDiv.comp ((Procedure.ratNeg.comp ((gradientProgram rho a).comp inputSampleProgram)).pair
    (denominatorProgram rho))
noncomputable opaque preparedEnvironmentProgram (rho : ℕ) : Procedure environmentCode environmentCode
    (fun e => (precision rho e.1,e.2)) :=
  ((innerPrecisionProgram rho).comp envPrecisionProgram).pair envDataProgram
noncomputable opaque preparedInputProgram (rho : ℕ) : Procedure inputCode inputCode
    (fun x => ((precision rho x.1.1,x.1.2),x.2)) :=
  ((preparedEnvironmentProgram rho).comp inputEnvironmentProgram).pair inputTimePointProgram
noncomputable opaque componentProgram (rho : ℕ) (a : Fin 3) : Procedure inputCode ratCode
    (fun x => component rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.1 x.2.2 a) :=
  by
    let p := (coreComponentProgram rho a).comp (preparedInputProgram rho)
    exact p.congrFun (by intro x; rfl)
noncomputable opaque program (rho : ℕ) : Procedure inputCode tripleCode
    (fun x => value rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.1 x.2.2) :=
  (componentProgram rho 0).pair ((componentProgram rho 1).pair (componentProgram rho 2))

noncomputable def certificate (rho : ℕ) : Turing.TM2ComputableInPolyTime inputCode tripleCode
    (fun x => value rho x.1.1 x.1.2.1.1 x.1.2.1.2 x.1.2.2 x.2.1 x.2.2) := (program rho).toTM2

end ContinuumCoulomb.ManufacturedVelocityEvaluation

end OAI
