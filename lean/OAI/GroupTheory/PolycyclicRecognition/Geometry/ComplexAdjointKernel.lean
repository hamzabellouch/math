import OAI.GroupTheory.PolycyclicRecognition.Geometry.ComplexAdjointWeights
import Mathlib.Algebra.Lie.Engel
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace OAI

/-! # The nilpotent kernel of the complex adjoint weights

Complex weights retain rotational directions. Their common real kernel is
nilpotent by triangular matrices, faithful scalar extension, and Engel's theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {n : ℕ}

structure ComplexTriangularAdjoint (L : Type*) [LieRing L] [LieAlgebra ℝ L] (n : ℕ) where
  basis : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)
  upper : ∀ x : ℂ ⊗[ℝ] L,
    (LinearMap.toMatrix basis basis (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) x)).IsUpperTriangular

namespace ComplexTriangularAdjoint
variable (T : ComplexTriangularAdjoint L n)

def weightMap : L →ₗ[ℝ] (Fin n → ℂ) where
  toFun x i := complexifiedAdjointMatrix L T.basis x i i
  map_add' x y := by
    ext i
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i)
      ((complexifiedAdjointMatrix L T.basis).map_add x y)
  map_smul' r x := by
    ext i
    exact congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i i)
      ((complexifiedAdjointMatrix L T.basis).map_smul r x)

private theorem mul_diag (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

@[simp] theorem weightMap_lie (x y : L) : T.weightMap ⁅x, y⁆ = 0 := by
  ext i
  change complexifiedAdjointMatrix L T.basis ⁅x, y⁆ i i = 0
  rw [LieHom.map_lie]
  change (complexifiedAdjointMatrix L T.basis x * complexifiedAdjointMatrix L T.basis y -
    complexifiedAdjointMatrix L T.basis y * complexifiedAdjointMatrix L T.basis x) i i = 0
  simp only [complexifiedAdjointMatrix_apply]
  rw [Matrix.sub_apply, mul_diag _ _ (T.upper _) (T.upper _),
    mul_diag _ _ (T.upper _) (T.upper _), mul_comm, sub_self]

def kernelIdeal : LieIdeal ℝ L where
  __ := T.weightMap.ker
  lie_mem := by intro x y _; exact T.weightMap_lie x y

@[simp] theorem mem_kernelIdeal (x : L) :
    x ∈ T.kernelIdeal ↔ T.weightMap x = 0 := Iff.rfl

private theorem matrix_nilpotent (x : L) (hx : x ∈ T.kernelIdeal) :
    IsNilpotent (complexifiedAdjointMatrix L T.basis x) := by
  let A := complexifiedAdjointMatrix L T.basis x
  have hz (i : Fin n) : A i i = 0 := congrFun hx i
  have hp : A.charpoly = Polynomial.X ^ n := by
    rw [Matrix.charpoly_of_isUpperTriangular A (T.upper _)]
    simp [hz]
  refine ⟨n, ?_⟩
  have h := Matrix.aeval_self_charpoly A
  simpa only [hp, map_pow, Polynomial.aeval_X] using h

/-- Vanishing complex weights force the original real adjoint operator to be nilpotent. -/
theorem ad_nilpotent (x : L) (hx : x ∈ T.kernelIdeal) :
    IsNilpotent (LieAlgebra.ad ℝ L x) := by
  obtain ⟨k, hk⟩ := T.matrix_nilpotent x hx
  let C := ℂ ⊗[ℝ] L
  let j := complexificationLieHom L
  let D := LieAlgebra.ad ℂ C (j x)
  have hD : D ^ k = 0 := by
    apply (LinearMap.toMatrixAlgEquiv T.basis).injective
    rw [map_pow, map_zero]
    exact hk
  have intertwine (m : ℕ) (y : L) :
      j (((LieAlgebra.ad ℝ L x) ^ m) y) = (D ^ m) (j y) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      exact (j.map_lie x _).trans (congrArg D ih)
  refine ⟨k, ?_⟩
  ext y
  apply complexificationLieHom_injective L
  rw [intertwine, hD]
  simp [j]

/-- The common kernel is a nilpotent Lie ideal, even when weights are nonreal. -/
theorem kernelIdeal_nilpotent [FiniteDimensional ℝ L] :
    LieRing.IsNilpotent T.kernelIdeal := by
  have : LieModule.IsNilpotent T.kernelIdeal L :=
    (LieModule.isNilpotent_iff_forall' (R := ℝ)).mpr fun x =>
      T.ad_nilpotent x x.property
  exact T.kernelIdeal.incl_injective.lieModuleIsNilpotent
    (f := LieHom.id) (g := T.kernelIdeal.incl.toLinearMap) (fun _ _ => rfl)

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI
