import OAI.Algebra.Finitistic.Encoding.QuadraticEncoding
import Mathlib.LinearAlgebra.Pi

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ}
variable {Y : Type v} [AddCommGroup Y] [Module k Y]

/-- An arbitrary vector-space representation of the presented quadratic algebra. -/
structure Representation (P : Relations k d t) (Y : Type v)
    [AddCommGroup Y] [Module k Y] where
  generator : Fin d → Module.End k Y
  relation : ∀ j, (∑ h, ∑ l, P.quadratic j h l • (generator h * generator l)) +
    (∑ h, P.linear j h • generator h) + P.constant j • (1 : Module.End k Y) = 0

namespace Representation
variable {P : Relations k d t} (X : Representation P Y)

def arrowAction : Arrows k d →ₗ[k] Module.End k Y :=
  ∑ i, (LinearMap.proj i).smulRight (Fin.cases 1 X.generator i)

@[simp] theorem arrowAction_basis (i : Fin (d+1)) :
    X.arrowAction (basis i) = Fin.cases 1 X.generator i := by
  classical
  simp [arrowAction, basis, Pi.single_apply]

def rawPathAction : Paths k d →ₗ[k] Module.End k Y :=
  TensorProduct.lift ((LinearMap.mul k (Module.End k Y)).compl₁₂ X.arrowAction X.arrowAction)

@[simp] theorem rawPathAction_tmul (w v : Arrows k d) :
    X.rawPathAction (w ⊗ₜ[k] v) = X.arrowAction w * X.arrowAction v := rfl

 theorem relations_killed : relationSpace P ≤ X.rawPathAction.ker := by
  rw [relationSpace, Submodule.span_le]
  rintro z (⟨h, rfl⟩ | ⟨j, rfl⟩)
  · simp [LinearMap.mem_ker, commutation]
  · simpa [LinearMap.mem_ker, homogenized] using X.relation j

/-- The actual descended length-two action, using the proved relation ideal. -/
def pathAction : (Paths k d ⧸ relationSpace P) →ₗ[k] Module.End k Y :=
  (relationSpace P).liftQ X.rawPathAction X.relations_killed

@[simp] theorem pathAction_mk (z : Paths k d) :
    X.pathAction ((relationSpace P).mkQ z) = X.rawPathAction z := rfl

@[simp] theorem pathAction_composition (w v : Arrows k d) :
    X.pathAction (composition P w v) = X.arrowAction w * X.arrowAction v := rfl

/-- Three copies of Y, with its representation kept in the type. -/
def Evaluation (_X : Representation P Y) := Y × Y × Y
instance : AddCommGroup X.Evaluation := inferInstanceAs (AddCommGroup (Y × Y × Y))
instance : Module k X.Evaluation := inferInstanceAs (Module k (Y × Y × Y))

@[simp] theorem evaluation_add (y z : X.Evaluation) :
    y + z = (y.1+z.1,y.2.1+z.2.1,y.2.2+z.2.2) := rfl
@[simp] theorem evaluation_zero : (0 : X.Evaluation) = (0,0,0) := rfl
@[simp] theorem evaluation_smul (c : k) (y : X.Evaluation) :
    c • y = (c • y.1,c • y.2.1,c • y.2.2) := rfl

def act (a : B P) (y : X.Evaluation) : X.Evaluation :=
  (a.1 • y.1,
   X.arrowAction a.2.2.2.1 y.1 + a.2.1 • y.2.1,
   X.pathAction a.2.2.2.2.2 y.1 + X.arrowAction a.2.2.2.2.1 y.2.1 + a.2.2.1 • y.2.2)

instance evaluationModule : Module (B P) X.Evaluation where
  smul := X.act
  one_smul y := by
    change X.act (ThreeVertexAlgebra.unit (composition P)) y = y
    rcases y with ⟨a,b,c⟩
    simp [act, ThreeVertexAlgebra.unit]; rfl
  mul_smul a b y := by
    change X.act (ThreeVertexAlgebra.mul (composition P) a b) y = X.act a (X.act b y)
    apply Prod.ext
    · simp [act, ThreeVertexAlgebra.mul, mul_smul]
    apply Prod.ext
    · simp [act, ThreeVertexAlgebra.mul, map_add, map_smul, smul_add, smul_smul]
      module
    · simp [act, ThreeVertexAlgebra.mul, map_add, map_smul, smul_add, smul_smul,
        Module.End.mul_apply]
      module
  smul_zero a := by
    change X.act a (0,0,0) = (0,0,0)
    simp [act]; rfl
  smul_add a y z := by
    change X.act a (y.1+z.1,y.2.1+z.2.1,y.2.2+z.2.2) =
      ((X.act a y).1+(X.act a z).1,(X.act a y).2.1+(X.act a z).2.1,
       (X.act a y).2.2+(X.act a z).2.2)
    apply Prod.ext
    · simp [act, smul_add]
    apply Prod.ext <;> simp [act, smul_add, map_add] <;> abel
  add_smul a b y := by
    change X.act (a+b) y =
      ((X.act a y).1+(X.act b y).1,(X.act a y).2.1+(X.act b y).2.1,
       (X.act a y).2.2+(X.act b y).2.2)
    rw [ThreeVertexAlgebra.add_eq]
    apply Prod.ext
    · simp [act, add_smul]
    apply Prod.ext <;> simp [act, add_smul, map_add] <;> abel
  zero_smul y := by
    change X.act (0,0,0,0,0,0) y = (0,0,0)
    simp [act]; rfl

theorem smul_eq (a : B P) (y : X.Evaluation) : a • y = X.act a y := rfl


instance : IsScalarTower k (B P) X.Evaluation where
  smul_assoc c a y := by
    change X.act (c • a) y = c • X.act a y
    rw [ThreeVertexAlgebra.smul_eq, evaluation_smul]
    apply Prod.ext
    · simp [act, mul_smul]
    apply Prod.ext <;> simp [act, smul_add, smul_smul]

instance : SMulCommClass k (B P) X.Evaluation where
  smul_comm c a y := by
    change c • X.act a y = X.act a (c • y)
    rw [evaluation_smul, evaluation_smul]
    apply Prod.ext
    · simp [act, smul_comm c a.1]
    apply Prod.ext <;> simp [act, smul_add, smul_smul, mul_comm]

instance [FiniteDimensional k Y] : FiniteDimensional k X.Evaluation :=
  inferInstanceAs (FiniteDimensional k (Y × Y × Y))

@[simp] theorem vertex0_smul (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) 0 • y = (y.1,0,0) := by
  simp [smul_eq, act, ThreeVertexAlgebra.vertex]; rfl
@[simp] theorem vertex1_smul (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) 1 • y = (0,y.2.1,0) := by
  simp [smul_eq, act, ThreeVertexAlgebra.vertex]; rfl
@[simp] theorem vertex2_smul (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) 2 • y = (0,0,y.2.2) := by
  simp [smul_eq, act, ThreeVertexAlgebra.vertex]; rfl

@[simp] theorem arrow01_smul (i : Fin (d+1)) (y : X.Evaluation) :
    arrow01 P i • y = (0, (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator i) y.1, 0) := by
  simp [smul_eq, act, arrow01]; rfl
@[simp] theorem arrow12_smul (i : Fin (d+1)) (y : X.Evaluation) :
    arrow12 P i • y = (0, 0, (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator i) y.2.1) := by
  simp [smul_eq, act, arrow12]; rfl

@[simp] theorem s_smul (y : X.Evaluation) : arrow01 P 0 • y = (0,y.1,0) := by
  simp; rfl
@[simp] theorem s'_smul (y : X.Evaluation) : arrow12 P 0 • y = (0,0,y.2.1) := by
  simp; rfl
@[simp] theorem generator01_smul (h : Fin d) (y : X.Evaluation) :
    arrow01 P h.succ • y = (0,X.generator h y.1,0) := by simp; rfl
@[simp] theorem generator12_smul (h : Fin d) (y : X.Evaluation) :
    arrow12 P h.succ • y = (0,0,X.generator h y.2.1) := by simp; rfl

@[simp] theorem pathMap_smul (z : Paths k d) (y : X.Evaluation) :
    pathMap P z • y = (0,0,X.rawPathAction z y.1) := by
  simp [smul_eq, act, pathMap, lengthTwo, pathAction]; rfl

/-- Inclusion of the copy of Y at each vertex. -/
def inclusion (i : Fin 3) : Y →ₗ[k] X.Evaluation where
  toFun y := match i with
    | 0 => (y,0,0)
    | 1 => (0,y,0)
    | 2 => (0,0,y)
  map_add' y z := by fin_cases i <;> rw [evaluation_add] <;> simp <;> rfl
  map_smul' c y := by fin_cases i <;> rw [evaluation_smul] <;> simp <;> rfl

def projection (i : Fin 3) : X.Evaluation →ₗ[k] Y where
  toFun y := match i with
    | 0 => y.1
    | 1 => y.2.1
    | 2 => y.2.2
  map_add' y z := by fin_cases i <;> rfl
  map_smul' c y := by fin_cases i <;> rfl

@[simp] theorem projection_inclusion (i : Fin 3) (y : Y) :
    X.projection i (X.inclusion i y) = y := by fin_cases i <;> rfl

theorem vertex_smul (i : Fin 3) (y : X.Evaluation) :
    ThreeVertexAlgebra.vertex (composition P) i • y = X.inclusion i (X.projection i y) := by
  fin_cases i <;> simp [inclusion, projection] <;> rfl

/-- The vertex space e_i M(Y), as an actual k-subspace of the constructed module. -/
def vertexSpace (i : Fin 3) : Submodule k X.Evaluation := (X.inclusion i).range

def vertexEquiv (i : Fin 3) : Y ≃ₗ[k] X.vertexSpace i :=
  LinearEquiv.ofInjective (X.inclusion i) (Function.LeftInverse.injective
    (X.projection_inclusion i))
end Representation
end LittleFinitistic.QuadraticEncoding

end

end OAI
