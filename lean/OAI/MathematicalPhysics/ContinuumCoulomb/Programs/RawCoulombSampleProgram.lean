import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RawCoulombSample
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalSixQuadrature

namespace OAI

/-! Literal polynomial programs for the Coulomb samples and their
six-coordinate summation. -/

namespace ContinuumCoulomb.RawCoulombSample
open ExactQuantumFactoring.BitStackProgram CappedKernelProgram

abbrev Settings := (ℕ × ℕ) × ((ℕ × ℚ) × Triple)
abbrev Input := Settings × (Triple × Triple)
abbrev DifferenceInput := (Triple × Triple) × Triple

def settingsCode : Settings → List Bool :=
  prodCode (prodCode unaryCode unaryCode) (prodCode (prodCode unaryCode ratCode) tripleCode)
def inputCode : Input → List Bool := prodCode settingsCode (prodCode tripleCode tripleCode)
def differenceCode : DifferenceInput → List Bool := prodCode (prodCode tripleCode tripleCode) tripleCode

def evaluate (rho : ℕ) (z : Input) : ℚ :=
  value rho z.1.1.1 z.1.1.2 z.1.2.1.1 z.1.2.1.2 z.1.2.2 z.2.1 z.2.2

noncomputable opaque firstCoordinate : Procedure tripleCode ratCode Prod.fst :=
  Procedure.first ratCode (prodCode ratCode ratCode)
noncomputable opaque secondCoordinate : Procedure tripleCode ratCode (fun x => x.2.1) :=
  (Procedure.first ratCode ratCode).comp (Procedure.second ratCode (prodCode ratCode ratCode))
noncomputable opaque thirdCoordinate : Procedure tripleCode ratCode (fun x => x.2.2) :=
  (Procedure.second ratCode ratCode).comp (Procedure.second ratCode (prodCode ratCode ratCode))

noncomputable opaque differenceProgram : Procedure differenceCode tripleCode
    (fun z => difference z.1.1 z.1.2 z.2) := by
  let xy := Procedure.first (prodCode tripleCode tripleCode) tripleCode
  let x := (Procedure.first tripleCode tripleCode).comp xy
  let y := (Procedure.second tripleCode tripleCode).comp xy
  let s := Procedure.second (prodCode tripleCode tripleCode) tripleCode
  let d0 := Procedure.ratSub.comp
    ((Procedure.ratSub.comp ((firstCoordinate.comp x).pair (firstCoordinate.comp y))).pair
      (firstCoordinate.comp s))
  let d1 := Procedure.ratSub.comp
    ((Procedure.ratSub.comp ((secondCoordinate.comp x).pair (secondCoordinate.comp y))).pair
      (secondCoordinate.comp s))
  let d2 := Procedure.ratSub.comp
    ((Procedure.ratSub.comp ((thirdCoordinate.comp x).pair (thirdCoordinate.comp y))).pair
      (thirdCoordinate.comp s))
  exact (d0.pair (d1.pair d2)).congrFun (by intro z; rfl)

noncomputable opaque sampleProgram (rho : ℕ) : Procedure inputCode ratCode (evaluate rho) := by
  let e := Procedure.first settingsCode (prodCode tripleCode tripleCode)
  let xy := Procedure.second settingsCode (prodCode tripleCode tripleCode)
  let x := (Procedure.first tripleCode tripleCode).comp xy
  let y := (Procedure.second tripleCode tripleCode).comp xy
  let rp := (Procedure.first (prodCode unaryCode unaryCode)
    (prodCode (prodCode unaryCode ratCode) tripleCode)).comp e
  let ks := (Procedure.second (prodCode unaryCode unaryCode)
    (prodCode (prodCode unaryCode ratCode) tripleCode)).comp e
  let kp := (Procedure.first (prodCode unaryCode ratCode) tripleCode).comp ks
  let s := (Procedure.second (prodCode unaryCode ratCode) tripleCode).comp ks
  let dx := (RawDensitySample.program rho).comp (rp.pair x)
  let dy := (RawDensitySample.program rho).comp (rp.pair y)
  let diff := differenceProgram.comp (xy.pair s)
  let kernel := CappedKernelProgram.program.comp (kp.pair diff)
  exact (Procedure.ratMul.comp ((Procedure.ratMul.comp (dx.pair dy)).pair kernel)).congrFun
    (by intro z; rfl)

def sixEvaluator (rho : ℕ) : RationalSixQuadrature.Evaluator Settings :=
  fun e a b c d f g => evaluate rho (e, ((a, b, c), (d, f, g)))

abbrev SixInput := (((Settings × RationalSixQuadrature.Pair) × RationalSixQuadrature.Pair) × ℚ) × ℚ
def sixInputCode : SixInput → List Bool :=
  prodCode (prodCode (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode) ratCode) ratCode

def sixInput (z : SixInput) : Input :=
  (z.1.1.1.1, ((z.1.1.1.2.1, z.1.1.1.2.2, z.1.1.2.1), (z.1.1.2.2, z.1.2, z.2)))

noncomputable opaque sixInputProgram : Procedure sixInputCode inputCode sixInput := by
  let top := Procedure.first
    (prodCode (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
      RationalSixQuadrature.pairCode) ratCode) ratCode
  let four := (Procedure.first (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode) ratCode).comp top
  let two := (Procedure.first (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode).comp four
  let e := (Procedure.first settingsCode RationalSixQuadrature.pairCode).comp two
  let ab := (Procedure.second settingsCode RationalSixQuadrature.pairCode).comp two
  let cd := (Procedure.second (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode).comp four
  let a := (Procedure.first ratCode ratCode).comp ab
  let b := (Procedure.second ratCode ratCode).comp ab
  let c := (Procedure.first ratCode ratCode).comp cd
  let d := (Procedure.second ratCode ratCode).comp cd
  let f := (Procedure.second (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
    RationalSixQuadrature.pairCode) ratCode).comp top
  let g := Procedure.second
    (prodCode (prodCode (prodCode settingsCode RationalSixQuadrature.pairCode)
      RationalSixQuadrature.pairCode) ratCode) ratCode
  exact (e.pair ((a.pair (b.pair c)).pair (d.pair (f.pair g)))).congrFun (by intro z; rfl)

noncomputable opaque sixSampleProgram (rho : ℕ) : Procedure sixInputCode ratCode
    (fun z => RationalSixQuadrature.inner (sixEvaluator rho) z.1.1 z.1.2 z.2) :=
  ((sampleProgram rho).comp sixInputProgram).congrFun (by intro z; rfl)

noncomputable opaque quadratureProgram (rho : ℕ) :
    Procedure (RationalRectangleProgram.inputCode settingsCode)
      ratCode (RationalSixQuadrature.value (sixEvaluator rho)) :=
  RationalSixQuadrature.program settingsCode (sixEvaluator rho) (sixSampleProgram rho)

noncomputable def quadratureCertificate (rho : ℕ) :
    Turing.TM2ComputableInPolyTime (RationalRectangleProgram.inputCode settingsCode)
      ratCode (RationalSixQuadrature.value (sixEvaluator rho)) :=
  (quadratureProgram rho).toTM2

end ContinuumCoulomb.RawCoulombSample

end OAI
