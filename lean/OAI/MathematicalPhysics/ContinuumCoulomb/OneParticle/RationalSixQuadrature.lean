import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalRectangleProgram

namespace OAI

/-! Six-coordinate rational cubature, as three literal rectangle programs.
The same finite mesh is retained in each register environment. -/

namespace ContinuumCoulomb.RationalSixQuadrature
open ExactQuantumFactoring.BitStackProgram

variable {E : Type}
abbrev Pair := ℚ × ℚ
abbrev Input (E : Type) := RationalRectangleProgram.Input E
abbrev Evaluator (E : Type) := E → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ

def pairCode : Pair → List Bool := prodCode ratCode ratCode

def augment (x : Input E) (a b : ℚ) : Input (E × Pair) :=
  (x.1, ((x.2.1, (a, b)), x.2.2))

def remember (x : Input E) : Input (Input E) := (x.1, (x, x.2.2))

def inner (f : Evaluator E) (e : (E × Pair) × Pair) (a b : ℚ) : ℚ :=
  f e.1.1 e.1.2.1 e.1.2.2 e.2.1 e.2.2 a b

def middle (f : Evaluator E) (x : Input (E × Pair)) (a b : ℚ) : ℚ :=
  RationalRectangleProgram.value (inner f) (augment x a b)

def outer (f : Evaluator E) (x : Input E) (a b : ℚ) : ℚ :=
  RationalRectangleProgram.value (middle f) (remember (augment x a b))

def value (f : Evaluator E) (x : Input E) : ℚ :=
  RationalRectangleProgram.value (outer f) (remember x)

noncomputable opaque augmentProgram (ce : E → List Bool) :
    Procedure (prodCode (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode)
      (RationalRectangleProgram.inputCode (prodCode ce pairCode))
      (fun x => augment x.1.1 x.1.2 x.2) := by
  let xa := Procedure.first (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode
  let x := (Procedure.first (RationalRectangleProgram.inputCode ce) ratCode).comp xa
  let a := (Procedure.second (RationalRectangleProgram.inputCode ce) ratCode).comp xa
  let b := Procedure.second (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode
  let n := (Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let env := (Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)).comp x
  let data := (Procedure.first ce pairCode).comp env
  let mesh := (Procedure.second ce pairCode).comp env
  exact (n.pair ((data.pair (a.pair b)).pair mesh)).congrFun (by intro q; rfl)

noncomputable opaque rememberProgram (ce : E → List Bool) :
    Procedure (RationalRectangleProgram.inputCode ce)
      (RationalRectangleProgram.inputCode (RationalRectangleProgram.inputCode ce)) remember := by
  let n := Procedure.first unaryCode (RationalQuadratureProgram.environmentCode ce)
  let env := Procedure.second unaryCode (RationalQuadratureProgram.environmentCode ce)
  let mesh := (Procedure.second ce pairCode).comp env
  exact (n.pair ((Procedure.identity (RationalRectangleProgram.inputCode ce)).pair mesh)).congrFun
    (by intro q; rfl)

noncomputable opaque middleProgram (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode (prodCode ce pairCode) pairCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (prodCode (prodCode (RationalRectangleProgram.inputCode (prodCode ce pairCode)) ratCode) ratCode)
      ratCode (fun x => middle f x.1.1 x.1.2 x.2) :=
  ((RationalRectangleProgram.program (prodCode (prodCode ce pairCode) pairCode) (inner f) p).comp
    (augmentProgram (prodCode ce pairCode))).congrFun (by intro q; rfl)

noncomputable opaque outerProgram (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode (prodCode ce pairCode) pairCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (prodCode (prodCode (RationalRectangleProgram.inputCode ce) ratCode) ratCode)
      ratCode (fun x => outer f x.1.1 x.1.2 x.2) := by
  let rectangle := RationalRectangleProgram.program
    (RationalRectangleProgram.inputCode (prodCode ce pairCode)) (middle f) (middleProgram ce f p)
  exact (rectangle.comp ((rememberProgram (prodCode ce pairCode)).comp (augmentProgram ce))).congrFun
    (by intro q; rfl)

noncomputable opaque program (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode (prodCode ce pairCode) pairCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Procedure (RationalRectangleProgram.inputCode ce) ratCode (value f) :=
  ((RationalRectangleProgram.program (RationalRectangleProgram.inputCode ce) (outer f)
    (outerProgram ce f p)).comp (rememberProgram ce)).congrFun (by intro q; rfl)

noncomputable def certificate (ce : E → List Bool) (f : Evaluator E)
    (p : Procedure (prodCode (prodCode (prodCode (prodCode ce pairCode) pairCode) ratCode) ratCode)
      ratCode (fun x => inner f x.1.1 x.1.2 x.2)) :
    Turing.TM2ComputableInPolyTime (RationalRectangleProgram.inputCode ce) ratCode (value f) :=
  (program ce f p).toTM2


theorem value_cast (f : Evaluator E) (x : Input E) :
    (value f x : ℝ) =
      UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1 (fun i j =>
        UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1 (fun k l =>
          UniformQuadrature.rectangleSum (x.2.2.2 : ℝ) (x.2.2.2 : ℝ) x.1 x.1 (fun m n =>
            (f x.2.1
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 i)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 j)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 k)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 l)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 m)
              (RationalQuadratureProgram.node x.2.2.1 x.2.2.2 n) : ℝ)))) := by
  simp only [value, outer, middle, inner, remember, augment,
    RationalRectangleProgram.value_cast]

end ContinuumCoulomb.RationalSixQuadrature

end OAI
