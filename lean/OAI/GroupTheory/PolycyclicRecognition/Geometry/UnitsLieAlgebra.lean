import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraHomLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponentialNaturality
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

namespace OAI

/-! # The actual tangent Lie algebra of algebra units

Differentiating the inclusion identifies the tangent Lie algebra with the
commutator algebra. This permits the proved nilpotent integration theorem
to target matrix units directly.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff
attribute [local instance 100] LieRing.ofAssociativeRing

variable (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def unitsLieHom : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ →ₗ⁅ℝ⁆ A :=
  unitsHomLieDifferential (MonoidHom.id Aˣ) Units.contMDiff_val

theorem unitsLieHom_apply (x : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ) : unitsLieHom A x = x := by
  change (mfderiv (𝓘(ℝ, A)) (𝓘(ℝ, A)) (Units.val : Aˣ → A) 1) x = x
  have he : (Units.val : Aˣ → A) = extChartAt (𝓘(ℝ, A)) (1 : Aˣ) := rfl
  rw [he, mfderiv_extChartAt_self]
  rfl

def unitsLieEquiv : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ ≃ₗ⁅ℝ⁆ A :=
  LieEquiv.ofBijective (unitsLieHom A)
    ⟨fun x y h => (unitsLieHom_apply A x).symm.trans (h.trans (unitsLieHom_apply A y)),
      fun x => ⟨x, unitsLieHom_apply A x⟩⟩

@[simp] theorem unitsLieEquiv_apply (x : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ) :
    unitsLieEquiv A x = x := unitsLieHom_apply A x

@[simp] theorem unitsLieEquiv_symm_apply (x : A) : (unitsLieEquiv A).symm x = x := by
  have h := (unitsLieEquiv A).apply_symm_apply x
  exact (unitsLieEquiv_apply A ((unitsLieEquiv A).symm x)).symm.trans h

variable [FiniteDimensional ℝ A]

theorem groupExponential_units (x : GroupLieAlgebra (𝓘(ℝ, A)) Aˣ) :
    groupExponential x = algebraExpUnit (unitsLieEquiv A x) :=
  hom_exp_eq_algebraExpUnit groupExponential_isGroupExponential (MonoidHom.id Aˣ)
    (unitsLieHom A).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (MonoidHom.id Aˣ) Units.contMDiff_val) x

end PolycyclicRecognition

end

end OAI
