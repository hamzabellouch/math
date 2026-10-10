import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalQuadratureProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RectangleQuadrature

namespace OAI

/-! A literal two-coordinate rational quadrature. The same mesh in both
coordinates is enough for the normalization and compact contact integrals. -/

namespace ContinuumCoulomb.RationalRectangleProgram
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}
abbrev Input (E : Type) := RationalQuadratureProgram.Input E

def inputCode (ce : E → List Bool) : Input E → List Bool :=
  RationalQuadratureProgram.inputCode ce

def lineInput (x : Input E × ℚ) : RationalQuadratureProgram.Input (E × ℚ) :=
  (x.1.1, ((x.1.2.1, x.2), x.1.2.2))

def line (evaluate : E → ℚ → ℚ → ℚ) (e : Input E) (x : ℚ) : ℚ :=
  RationalQuadratureProgram.value (fun q y => evaluate q.1 q.2 y) (lineInput (e, x))

def outerInput (x : Input E) : RationalQuadratureProgram.Input (Input E) :=
  (x.1, (x, x.2.2))

def value (evaluate : E → ℚ → ℚ → ℚ) (x : Input E) : ℚ :=
  RationalQuadratureProgram.value (line evaluate) (outerInput x)

noncomputable opaque lineInputProgram (ce : E → List Bool) :
    Procedure (prodCode (inputCode ce) ratCode)
      (RationalQuadratureProgram.inputCode (prodCode ce ratCode)) lineInput := by
  let e := Procedure.first (inputCode ce) ratCode
  let x := Procedure.second (inputCode ce) ratCode
  let n := (Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)).comp e
  let env := (Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)).comp e
  let data := (Procedure.first ce (prodCode ratCode ratCode)).comp env
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact (n.pair ((data.pair x).pair mesh)).congrFun (by intro q; rfl)

noncomputable opaque outerInputProgram (ce : E → List Bool) :
    Procedure (inputCode ce) (RationalQuadratureProgram.inputCode (inputCode ce)) outerInput := by
  let n := Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact (n.pair ((Procedure.identity (inputCode ce)).pair mesh)).congrFun (by intro q; rfl)

noncomputable opaque program (ce : E → List Bool) (evaluate : E → ℚ → ℚ → ℚ)
    (p : Procedure (prodCode (prodCode ce ratCode) ratCode) ratCode
      (fun q => evaluate q.1.1 q.1.2 q.2)) :
    Procedure (inputCode ce) ratCode (value evaluate) := by
  let inner := (RationalQuadratureProgram.program (prodCode ce ratCode)
    (fun q y => evaluate q.1 q.2 y) p).comp (lineInputProgram ce)
  exact ((RationalQuadratureProgram.program (inputCode ce) (line evaluate)
    inner).comp (outerInputProgram ce)).congrFun (by intro q; rfl)

noncomputable def certificate (ce : E → List Bool) (evaluate : E → ℚ → ℚ → ℚ)
    (p : Procedure (prodCode (prodCode ce ratCode) ratCode) ratCode
      (fun q => evaluate q.1.1 q.1.2 q.2)) :
    Turing.TM2ComputableInPolyTime (inputCode ce) ratCode (value evaluate) :=
  (program ce evaluate p).toTM2

theorem value_cast (evaluate : E → ℚ → ℚ → ℚ) (x : Input E) :
    (value evaluate x : ℝ) =
      UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1
        (fun i j => (evaluate x.2.1
          (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
          (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j) : ℝ)) := by
  simp [value, outerInput, line, lineInput, RationalQuadratureProgram.value,
    RationalQuadratureProgram.sample, UniformQuadrature.rectangleSum, UniformQuadrature.sampleSum]

end ContinuumCoulomb.RationalRectangleProgram

end OAI
