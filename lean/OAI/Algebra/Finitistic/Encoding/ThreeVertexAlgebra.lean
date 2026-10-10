import OAI.Algebra.Finitistic.Encoding.DirectedBound
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u v
variable {k V W U : Type u} [Field k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup U] [Module k U]

/-- Coordinates by the six possible path endpoints: three vertices,
0-to-1 arrows, 1-to-2 arrows, and length-two paths modulo relations. -/
abbrev ThreeVertexAlgebra (_μ : W →ₗ[k] V →ₗ[k] U) := k × k × k × V × W × U

namespace ThreeVertexAlgebra
variable (μ : W →ₗ[k] V →ₗ[k] U)

instance : AddCommGroup (ThreeVertexAlgebra μ) :=
  inferInstanceAs (AddCommGroup (k × k × k × V × W × U))
instance : Module k (ThreeVertexAlgebra μ) :=
  inferInstanceAs (Module k (k × k × k × V × W × U))

@[simp] theorem zero_eq : (0 : ThreeVertexAlgebra μ) = (0, 0, 0, 0, 0, 0) := rfl
@[simp] theorem add_eq (x y : ThreeVertexAlgebra μ) :
    x + y = (x.1+y.1, x.2.1+y.2.1, x.2.2.1+y.2.2.1,
      x.2.2.2.1+y.2.2.2.1, x.2.2.2.2.1+y.2.2.2.2.1,
      x.2.2.2.2.2+y.2.2.2.2.2) := rfl
@[simp] theorem smul_eq (c : k) (x : ThreeVertexAlgebra μ) :
    c • x = (c*x.1, c*x.2.1, c*x.2.2.1,
      c • x.2.2.2.1, c • x.2.2.2.2.1, c • x.2.2.2.2.2) := rfl

def mul (x y : ThreeVertexAlgebra μ) : ThreeVertexAlgebra μ :=
  (x.1 * y.1, x.2.1 * y.2.1, x.2.2.1 * y.2.2.1,
   y.1 • x.2.2.2.1 + x.2.1 • y.2.2.2.1,
   y.2.1 • x.2.2.2.2.1 + x.2.2.1 • y.2.2.2.2.1,
   y.1 • x.2.2.2.2.2 + μ x.2.2.2.2.1 y.2.2.2.1 + x.2.2.1 • y.2.2.2.2.2)

def unit : ThreeVertexAlgebra μ := (1, 1, 1, 0, 0, 0)

@[ext] theorem ext (x y : ThreeVertexAlgebra μ)
    (h0 : x.1 = y.1) (h1 : x.2.1 = y.2.1) (h2 : x.2.2.1 = y.2.2.1)
    (hv : x.2.2.2.1 = y.2.2.2.1) (hw : x.2.2.2.2.1 = y.2.2.2.2.1)
    (hu : x.2.2.2.2.2 = y.2.2.2.2.2) : x = y :=
  Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext hv (Prod.ext hw hu))))

instance : Ring (ThreeVertexAlgebra μ) where
  __ := (inferInstance : AddCommGroup (ThreeVertexAlgebra μ))
  mul := mul μ
  one := unit μ
  mul_assoc x y z := by
    change mul μ (mul μ x y) z = mul μ x (mul μ y z)
    apply Prod.ext <;> dsimp [mul]
    · ring
    apply Prod.ext
    · ring
    apply Prod.ext
    · ring
    apply Prod.ext
    · simp only [smul_add, smul_smul]; module
    apply Prod.ext
    · simp only [smul_add, smul_smul]; module
    · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_add, smul_smul]; module
  one_mul x := by
    change mul μ (unit μ) x = x
    apply Prod.ext <;> dsimp [mul, unit]
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext <;> simp
  mul_one x := by
    change mul μ x (unit μ) = x
    apply Prod.ext <;> dsimp [mul, unit]
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    apply Prod.ext <;> simp
  left_distrib x y z := by
    change mul μ x (y + z) = mul μ x y + mul μ x z
    rw [add_eq μ (mul μ x y) (mul μ x z), add_eq μ y z]
    ext <;> simp [mul, mul_add, smul_add, add_smul, map_add] <;> abel
  right_distrib x y z := by
    change mul μ (x + y) z = mul μ x z + mul μ y z
    rw [add_eq μ (mul μ x z) (mul μ y z), add_eq μ x y]
    ext <;> simp [mul, add_mul, smul_add, add_smul, map_add] <;> abel
  zero_mul x := by
    change (mul μ 0 x : k × k × k × V × W × U) = 0
    ext <;> simp [mul]
  mul_zero x := by
    change (mul μ x 0 : k × k × k × V × W × U) = 0
    ext <;> simp [mul]


@[simp] theorem mul_eq (x y : ThreeVertexAlgebra μ) : x * y = mul μ x y := rfl
@[simp] theorem one_eq : (1 : ThreeVertexAlgebra μ) = unit μ := rfl

instance : Algebra k (ThreeVertexAlgebra μ) where
  algebraMap :=
    { toFun := fun c => (c, c, c, 0, 0, 0)
      map_zero' := (zero_eq μ).symm
      map_one' := rfl
      map_add' := fun a b => by
        change ((a+b, a+b, a+b, 0, 0, 0) : ThreeVertexAlgebra μ) =
          (a, a, a, 0, 0, 0) + (b, b, b, 0, 0, 0)
        rw [add_eq μ]
        simp
      map_mul' := fun a b => by
        change ((a*b, a*b, a*b, 0, 0, 0) : ThreeVertexAlgebra μ) =
          mul μ (a, a, a, 0, 0, 0) (b, b, b, 0, 0, 0)
        simp [mul] }
  commutes' c x := by
    change mul μ (c, c, c, 0, 0, 0) x = mul μ x (c, c, c, 0, 0, 0)
    ext <;> simp [mul, mul_comm]
  smul_def' c x := by
    change c • x = mul μ (c, c, c, 0, 0, 0) x
    rw [smul_eq μ]
    simp [mul]

instance [FiniteDimensional k V] [FiniteDimensional k W] [FiniteDimensional k U] :
    FiniteDimensional k (ThreeVertexAlgebra μ) :=
  inferInstanceAs (FiniteDimensional k (k × k × k × V × W × U))

/-- The three vertex idempotents, in the manuscript's order. -/
def vertex : Fin 3 → ThreeVertexAlgebra μ
  | ⟨0, _⟩ => (1, 0, 0, 0, 0, 0)
  | ⟨1, _⟩ => (0, 1, 0, 0, 0, 0)
  | ⟨2, _⟩ => (0, 0, 1, 0, 0, 0)

def directedSystem : DirectedBound.DirectedSystem k (ThreeVertexAlgebra μ) 3 where
  e := vertex μ
  idem i := by fin_cases i <;> ext <;> simp [vertex, mul]
  orthogonal i j hij := by
    fin_cases i <;> fin_cases j <;> simp_all [vertex, mul]
  complete := by
    simp [Fin.sum_univ_succ, vertex, unit, add_eq μ]
  diagonal i a := by
    fin_cases i
    · exact ⟨a.1, by ext <;> simp [vertex, mul, smul_eq μ]⟩
    · exact ⟨a.2.1, by ext <;> simp [vertex, mul, smul_eq μ]⟩
    · exact ⟨a.2.2.1, by ext <;> simp [vertex, mul, smul_eq μ]⟩
  directed i j hij a := by
    fin_cases i <;> fin_cases j <;> simp_all [vertex, mul]

open CategoryTheory
/-- The three-vertex coordinate algebra has global dimension at most two on both sides. -/
theorem globalDimension_le_two :
    (⨆ N : ModuleCat.{max u v} (ThreeVertexAlgebra μ), projectiveDimension N) ≤ (2 : ℕ) ∧
    (⨆ N : ModuleCat.{max u v} (ThreeVertexAlgebra μ)ᵐᵒᵖ, projectiveDimension N) ≤ (2 : ℕ) :=
  (directedSystem μ).both_sides_globalDimension_le
end ThreeVertexAlgebra
end LittleFinitistic

end

end OAI
