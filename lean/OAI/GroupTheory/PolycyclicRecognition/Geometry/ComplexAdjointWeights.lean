import OAI.GroupTheory.PolycyclicRecognition.Geometry.SimultaneousAdjointBasis
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

namespace OAI

/-! # Complex adjoint weights for solvable real Lie algebras

The existing simultaneous-basis construction applies over the complex
numbers as well. Its restriction to real vectors supplies the weights whose
lifted group characters are used in the general solvable lattice argument.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped TensorProduct
open Module
attribute [local instance 100] LieRing.ofAssociativeRing

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L]

/-- The canonical real Lie homomorphism into the complexification. -/
def complexificationLieHom : L →ₗ⁅ℝ⁆ ℂ ⊗[ℝ] L :=
  { toLinearMap := TensorProduct.mk ℝ ℂ L 1
    map_lie' := by
      intro x y
      change 1 ⊗ₜ[ℝ] ⁅x, y⁆ = ⁅(1 : ℂ) ⊗ₜ[ℝ] x, (1 : ℂ) ⊗ₜ[ℝ] y⁆
      simp }

theorem complexificationLieHom_injective : Function.Injective (complexificationLieHom L) := by
  intro x y hxy
  change (1 : ℂ) ⊗ₜ[ℝ] x = (1 : ℂ) ⊗ₜ[ℝ] y at hxy
  apply sub_eq_zero.mp
  apply (Module.FaithfullyFlat.one_tmul_eq_zero_iff ℝ L (A := ℂ) (x - y)).mp
  simpa only [TensorProduct.tmul_sub, sub_eq_zero] using hxy

/-- A complex triangular basis of the actual complexified adjoint action. -/
theorem exists_complex_triangular_adjoint_basis [FiniteDimensional ℝ L]
    [LieAlgebra.IsSolvable L] :
    ∃ (n : ℕ) (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)),
      ∀ x : ℂ ⊗[ℝ] L,
        (LinearMap.toMatrix b b (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) x)).IsUpperTriangular := by
  exact exists_upperTriangular_lieModule_basis (𝕜 := ℂ) (ℂ ⊗[ℝ] L) (ℂ ⊗[ℝ] L)

/-- The complexified adjoint matrices, restricted to the original real algebra. -/
def complexifiedAdjointMatrix {n : ℕ} (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) :
    L →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℂ := by
  let j := (LinearMap.toMatrixAlgEquiv b).toLieEquiv.toLieHom.comp
    (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L))
  let jr : (ℂ ⊗[ℝ] L) →ₗ⁅ℝ⁆ Matrix (Fin n) (Fin n) ℂ :=
    { toLinearMap := j.toLinearMap.restrictScalars ℝ
      map_lie' := j.map_lie' }
  exact jr.comp (complexificationLieHom L)

@[simp] theorem complexifiedAdjointMatrix_apply {n : ℕ}
    (b : Basis (Fin n) ℂ (ℂ ⊗[ℝ] L)) (x : L) :
    complexifiedAdjointMatrix L b x =
      LinearMap.toMatrix b b (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] L) (1 ⊗ₜ[ℝ] x)) := rfl

end PolycyclicRecognition

end

end OAI
