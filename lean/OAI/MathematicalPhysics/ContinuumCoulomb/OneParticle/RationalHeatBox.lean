import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalHeatSample

namespace OAI

/-! Three literal nested quadratures for the heat representation of the
planar resolvent. The two spatial integrals run over `[-1,1]`, which
contains the support of the forcing. All sample counts are unary. -/

namespace ContinuumCoulomb.RationalHeatBox
open ExactQuantumFactoring.BitStackProgram
open RationalHeatSample

abbrev Settings := RationalHeatSample.Settings × (Point × ℕ)
abbrev PlaneEnvironment := Settings × ℚ
abbrev LineEnvironment := PlaneEnvironment × ℚ

def settingsCode : Settings → List Bool :=
  prodCode RationalHeatSample.settingsCode (prodCode pointCode unaryCode)

def planeCode : PlaneEnvironment → List Bool := prodCode settingsCode ratCode
def lineCode : LineEnvironment → List Bool := prodCode planeCode ratCode

def sample (e : LineEnvironment) (y₂ : ℚ) : ℚ :=
  RationalHeatSample.value (e.1.1.1, e.1.2, e.1.1.2.1, e.2, y₂)

def lineInput (e : PlaneEnvironment) (y₁ : ℚ) : RationalQuadratureProgram.Input LineEnvironment :=
  (e.1.2.2, (e, y₁), -1, 2 / (e.1.2.2 : ℚ))

def line (e : PlaneEnvironment) (y₁ : ℚ) : ℚ :=
  RationalQuadratureProgram.value sample (lineInput e y₁)

def planeInput (e : Settings) (t : ℚ) : RationalQuadratureProgram.Input PlaneEnvironment :=
  (e.2.2, (e, t), -1, 2 / (e.2.2 : ℚ))

def plane (e : Settings) (t : ℚ) : ℚ :=
  RationalQuadratureProgram.value line (planeInput e t)

abbrev Input := RationalQuadratureProgram.Input Settings

def inputCode : Input → List Bool := RationalQuadratureProgram.inputCode settingsCode

def value (x : Input) : ℚ := RationalQuadratureProgram.value plane x

noncomputable def sampleProgram :
    Procedure (prodCode lineCode ratCode) ratCode (fun x => sample x.1 x.2) := by
  let lineEnv := Procedure.first lineCode ratCode
  let y₂ := Procedure.second lineCode ratCode
  let planeEnv := (Procedure.first planeCode ratCode).comp lineEnv
  let y₁ := (Procedure.second planeCode ratCode).comp lineEnv
  let setting := (Procedure.first settingsCode ratCode).comp planeEnv
  let t := (Procedure.second settingsCode ratCode).comp planeEnv
  let constants := (Procedure.first RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp setting
  let pointAndCount := (Procedure.second RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp setting
  let point := (Procedure.first pointCode unaryCode).comp pointAndCount
  let args := constants.pair (t.pair (point.pair (y₁.pair y₂)))
  exact (RationalHeatSample.program.comp args).congrFun (by intro x; rfl)

noncomputable def lineInputProgram :
    Procedure (prodCode planeCode ratCode) (RationalQuadratureProgram.inputCode lineCode)
      (fun x => lineInput x.1 x.2) := by
  let e := Procedure.first planeCode ratCode
  let y := Procedure.second planeCode ratCode
  let setting := (Procedure.first settingsCode ratCode).comp e
  let pointAndCount := (Procedure.second RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp setting
  let N := (Procedure.second pointCode unaryCode).comp pointAndCount
  let count := Procedure.natToRat.comp (Procedure.unaryToBits.comp N)
  let two := Procedure.constant (prodCode planeCode ratCode) ratCode (2 : ℚ)
  let h := Procedure.ratDiv.comp (two.pair count)
  let a := Procedure.constant (prodCode planeCode ratCode) ratCode (-1 : ℚ)
  exact (N.pair ((e.pair y).pair (a.pair h))).congrFun (by intro x; rfl)

noncomputable def lineProgram :
    Procedure (prodCode planeCode ratCode) ratCode (fun x => line x.1 x.2) :=
  ((RationalQuadratureProgram.program lineCode sample sampleProgram).comp lineInputProgram).congrFun
    (by intro x; rfl)

noncomputable def planeInputProgram :
    Procedure (prodCode settingsCode ratCode) (RationalQuadratureProgram.inputCode planeCode)
      (fun x => planeInput x.1 x.2) := by
  let e := Procedure.first settingsCode ratCode
  let t := Procedure.second settingsCode ratCode
  let pointAndCount := (Procedure.second RationalHeatSample.settingsCode
    (prodCode pointCode unaryCode)).comp e
  let N := (Procedure.second pointCode unaryCode).comp pointAndCount
  let count := Procedure.natToRat.comp (Procedure.unaryToBits.comp N)
  let two := Procedure.constant (prodCode settingsCode ratCode) ratCode (2 : ℚ)
  let h := Procedure.ratDiv.comp (two.pair count)
  let a := Procedure.constant (prodCode settingsCode ratCode) ratCode (-1 : ℚ)
  exact (N.pair ((e.pair t).pair (a.pair h))).congrFun (by intro x; rfl)

noncomputable def planeProgram :
    Procedure (prodCode settingsCode ratCode) ratCode (fun x => plane x.1 x.2) :=
  ((RationalQuadratureProgram.program planeCode line lineProgram).comp planeInputProgram).congrFun
    (by intro x; rfl)

noncomputable def program : Procedure inputCode ratCode value :=
  (RationalQuadratureProgram.program settingsCode plane planeProgram).congrFun
    (by intro x; rfl)

noncomputable def certificate :
    Turing.TM2ComputableInPolyTime inputCode ratCode value := program.toTM2

end ContinuumCoulomb.RationalHeatBox

end OAI
