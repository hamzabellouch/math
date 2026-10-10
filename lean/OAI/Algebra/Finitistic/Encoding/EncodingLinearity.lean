import OAI.Algebra.Finitistic.Encoding.EncodingGenerators
import Mathlib.Algebra.Algebra.Tower

namespace OAI
noncomputable section
namespace LittleFinitistic.EncodingLinearity
open QuadraticEncoding
universe u v w
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module (B P) M] [Module (B P) N]
  [IsScalarTower k (B P) M] [IsScalarTower k (B P) N]

/-- Elements whose action commutes with a specified linear map form a subalgebra. -/
def intertwining (f : M →ₗ[k] N) : Subalgebra k (B P) where
  carrier := {b | ∀ x, f (b • x) = b • f x}
  zero_mem' := by intro x; simp only [zero_smul, map_zero]
  one_mem' := by intro x; simp only [one_smul]
  add_mem' := by
    intro a b ha hb x
    simp only [add_smul, map_add]
    rw [ha x, hb x]
  mul_mem' := by
    intro a b ha hb x
    simp only [mul_smul]
    rw [ha (b • x), hb x]
  algebraMap_mem' := by intro c x; simp only [IsScalarTower.algebraMap_smul, map_smul]

/-- Full B-linearity follows from the actual three vertex and two finite arrow lists.
Length-two actions require no additional hypothesis. -/
theorem map_smul (f : M →ₗ[k] N)
    (hv : ∀ i x, f (ThreeVertexAlgebra.vertex (composition P) i • x) =
      ThreeVertexAlgebra.vertex (composition P) i • f x)
    (h01 : ∀ a x, f (arrow01 P a • x) = arrow01 P a • f x)
    (h12 : ∀ a x, f (arrow12 P a • x) = arrow12 P a • f x)
    (b : B P) (x : M) : f (b • x) = b • f x := by
  have h := EncodingGenerators.eq_top P (intertwining P f) hv h01 h12
  have hb : b ∈ intertwining P f := by rw [h]; trivial
  exact hb x

/-- The original k-linear map, upgraded without changing its values. -/
def linearMap (f : M →ₗ[k] N)
    (hv : ∀ i x, f (ThreeVertexAlgebra.vertex (composition P) i • x) =
      ThreeVertexAlgebra.vertex (composition P) i • f x)
    (h01 : ∀ a x, f (arrow01 P a • x) = arrow01 P a • f x)
    (h12 : ∀ a x, f (arrow12 P a • x) = arrow12 P a • f x) : M →ₗ[B P] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_smul P f hv h01 h12

/-- A vector-space isomorphism respecting the finite generating actions is a
B-module isomorphism with exactly the original forward and inverse functions. -/
def linearEquiv (f : M ≃ₗ[k] N)
    (hv : ∀ i x, f (ThreeVertexAlgebra.vertex (composition P) i • x) =
      ThreeVertexAlgebra.vertex (composition P) i • f x)
    (h01 : ∀ a x, f (arrow01 P a • x) = arrow01 P a • f x)
    (h12 : ∀ a x, f (arrow12 P a • x) = arrow12 P a • f x) : M ≃ₗ[B P] N :=
  { linearMap P f.toLinearMap hv h01 h12, f.toEquiv with }
end LittleFinitistic.EncodingLinearity

end

end OAI
