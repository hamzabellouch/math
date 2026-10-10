import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalRectangleProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteCubeQuadrature

namespace OAI

/-! Three-coordinate rational cubature, using the already proved literal
one- and two-coordinate summation programs. -/

namespace ContinuumCoulomb.RationalTripleQuadrature
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}
abbrev Input (E : Type) := RationalQuadratureProgram.Input E
abbrev Evaluator (E : Type) := E → ℚ → ℚ → ℚ → ℚ

def augment (x : Input E) (a : ℚ) : Input (E×ℚ) :=
  (x.1,((x.2.1,a),x.2.2))

def remember (x : Input E) : Input (Input E) := (x.1,(x,x.2.2))

def inner (f : Evaluator E) (e : E×ℚ) (b c : ℚ) : ℚ := f e.1 e.2 b c

def outer (f : Evaluator E) (x : Input E) (a : ℚ) : ℚ :=
  RationalRectangleProgram.value (inner f) (augment x a)

def value (f : Evaluator E) (x : Input E) : ℚ :=
  RationalQuadratureProgram.value (outer f) (remember x)

noncomputable opaque augmentProgram (ce : E → List Bool) :
    Procedure (prodCode (RationalQuadratureProgram.inputCode ce) ratCode)
      (RationalQuadratureProgram.inputCode (prodCode ce ratCode))
      (fun x => augment x.1 x.2) := by
  let x := Procedure.first (RationalQuadratureProgram.inputCode ce) ratCode
  let a := Procedure.second (RationalQuadratureProgram.inputCode ce) ratCode
  let n := (Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let env := (Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let e := (Procedure.first ce (prodCode ratCode ratCode)).comp env
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact n.pair ((e.pair a).pair mesh)

noncomputable opaque rememberProgram (ce : E → List Bool) :
    Procedure (RationalQuadratureProgram.inputCode ce)
      (RationalQuadratureProgram.inputCode (RationalQuadratureProgram.inputCode ce)) remember := by
  let n := Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)
  let mesh := (Procedure.second ce (prodCode ratCode ratCode)).comp env
  exact n.pair ((Procedure.identity (RationalQuadratureProgram.inputCode ce)).pair mesh)

noncomputable opaque outerProgram (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode ce ratCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (prodCode (RationalQuadratureProgram.inputCode ce) ratCode) ratCode
      (fun x => outer f x.1 x.2) :=
  (RationalRectangleProgram.program (prodCode ce ratCode) (inner f) p).comp (augmentProgram ce)

noncomputable opaque program (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode ce ratCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (RationalQuadratureProgram.inputCode ce) ratCode (value f) :=
  (RationalQuadratureProgram.program (RationalQuadratureProgram.inputCode ce) (outer f)
    (outerProgram ce f p)).comp (rememberProgram ce)

noncomputable def certificate (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode ce ratCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Turing.TM2ComputableInPolyTime (RationalQuadratureProgram.inputCode ce) ratCode (value f) :=
  (program ce f p).toTM2

theorem value_cast (f : Evaluator E) (x : Input E) :
    (value f x:ℝ) = UniformQuadrature.cubeSample (x.2.2.2:ℝ) x.1 3 (fun v =>
      (f x.2.1 (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (v 0))
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (v 1))
        (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 (v 2)):ℝ)) := by
  simp only [value,RationalQuadratureProgram.value_cast,RationalQuadratureProgram.sample,
    outer,inner,remember,augment,RationalRectangleProgram.value_cast,
    UniformQuadrature.cubeSample,UniformQuadrature.rectangleSum,
    Fin.cons_zero,Fin.cons_one]
  rfl

end ContinuumCoulomb.RationalTripleQuadrature

end OAI
