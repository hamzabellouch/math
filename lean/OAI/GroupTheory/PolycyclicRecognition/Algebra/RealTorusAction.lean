import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealRotationTorus

namespace OAI

/-! # The compact rotational group acts on the real Lie algebra -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The compact torus action restricted to the original real form. -/
def realTorusOperator (z : realRotationTorus L H) : L →ₗ[ℝ] L :=
  (complexificationRealPart L).comp
    ((ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val).restrictScalars ℝ |>.comp
      (complexificationLieHom L).toLinearMap)

@[simp] theorem realTorusOperator_complexify (z : realRotationTorus L H) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] realTorusOperator L H z x =
      ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x) := by
  have hf : complexificationConjugation L
      (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x)) =
      ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x) := by
    rw [z.property]
    simp
  obtain ⟨y, hy⟩ := (complexification_conjugation_fixed_iff L _).mp hf
  change (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L
    (ComplexCartan.torusOperator (complexifiedSubalgebra L H) z.val.val ((1 : ℂ) ⊗ₜ[ℝ] x)) = _
  rw [hy, complexificationRealPart_tmul, Complex.one_re, one_smul]

@[simp] theorem realTorusOperator_one (x : L) : realTorusOperator L H 1 x = x := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realTorusOperator_complexify]
  exact ComplexCartan.torusOperator_one _ _

@[simp] theorem realTorusOperator_mul (z w : realRotationTorus L H) (x : L) :
    realTorusOperator L H (z * w) x = realTorusOperator L H z (realTorusOperator L H w x) := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realTorusOperator_complexify, realTorusOperator_complexify, realTorusOperator_complexify]
  exact ComplexCartan.torusOperator_mul _ _ _ _

theorem realTorusOperator_lie (z : realRotationTorus L H) (x y : L) :
    realTorusOperator L H z ⁅x, y⁆ = ⁅realTorusOperator L H z x, realTorusOperator L H z y⁆ := by
  apply complexificationLieHom_injective L
  rw [LieHom.map_lie]
  change (1 : ℂ) ⊗ₜ[ℝ] _ = ⁅(1 : ℂ) ⊗ₜ[ℝ] _, (1 : ℂ) ⊗ₜ[ℝ] _⁆
  rw [realTorusOperator_complexify, realTorusOperator_complexify, realTorusOperator_complexify]
  simpa only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] using
    z.val.property.1 ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y)

/-- Actual real Lie automorphisms, indexed by the compact torus. -/
def realTorusAutomorphism (z : realRotationTorus L H) : L ≃ₗ⁅ℝ⁆ L where
  toFun := realTorusOperator L H z
  map_add' := (realTorusOperator L H z).map_add
  map_smul' := (realTorusOperator L H z).map_smul
  invFun := realTorusOperator L H z⁻¹
  left_inv x := by rw [← realTorusOperator_mul, inv_mul_cancel, realTorusOperator_one]
  right_inv x := by rw [← realTorusOperator_mul, mul_inv_cancel, realTorusOperator_one]
  map_lie' := fun {x y} => realTorusOperator_lie L H z x y

/-- The underlying linear representation of the compact group. -/
def realTorusLinearAction : realRotationTorus L H →* (L ≃ₗ[ℝ] L) where
  toFun z := (realTorusAutomorphism L H z).toLinearEquiv
  map_one' := by ext x; exact realTorusOperator_one L H x
  map_mul' z w := by ext x; exact realTorusOperator_mul L H z w x

end PolycyclicRecognition

end

end OAI
