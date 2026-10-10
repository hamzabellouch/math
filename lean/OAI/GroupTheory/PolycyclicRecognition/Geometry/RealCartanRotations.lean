import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConjugateCartanWeights

namespace OAI

/-! # Cartan rotations preserve the actual real form -/

noncomputable section
namespace PolycyclicRecognition

open LieAlgebra LieModule Module
open scoped TensorProduct

variable (L : Type*) [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- The original real Cartan algebra inside its complexification. -/
def realCartanInComplex (h : H) : complexifiedSubalgebra L H :=
  ⟨1 ⊗ₜ[ℝ] (h : L), ⟨1 ⊗ₜ[ℝ] h, rfl⟩⟩

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
@[simp] theorem cartanConjugation_real (h : H) :
    cartanConjugation L H (realCartanInComplex L H h) = realCartanInComplex L H h := by
  apply Subtype.ext
  simp [cartanConjugation, realCartanInComplex]

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
theorem phase_conjugate_real (h : H) (χ : complexifiedSubalgebra L H → ℂ) :
    ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (conjugateCartanWeight L H χ) =
      star (ComplexCartan.phase (complexifiedSubalgebra L H) (realCartanInComplex L H h) χ) := by
  unfold ComplexCartan.phase conjugateCartanWeight
  rw [cartanConjugation_real]
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  congr 1
  simp [ComplexCartan.imaginaryPart]

/-- Conjugation commutes with rotations by real Cartan parameters. -/
theorem complex_rotation_conjugation (h : H) (x : ℂ ⊗[ℝ] L) :
    complexificationConjugation L
      (ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h) x) =
    ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (complexificationConjugation L x) := by
  apply ComplexCartan.root_induction (complexifiedSubalgebra L H) (x := x)
  · intro χ v hv
    rw [ComplexCartan.rotationLinear_apply _ _ χ hv, complexificationConjugation_smul,
      ComplexCartan.rotationLinear_apply_genWeight _ _ (conjugateCartanWeight L H χ)
        (conjugation_mem_genWeightSpace L H χ hv), phase_conjugate_real]
  · simp
  · intro v w hv hw
    simp only [map_add, hv, hw]

/-- Each rotation of a real vector is still real. -/
theorem exists_real_rotation (h : H) (x : L) :
    ∃ y : L,
      ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h)
        (1 ⊗ₜ[ℝ] x) = 1 ⊗ₜ[ℝ] y := by
  apply (complexification_conjugation_fixed_iff L _).mp
  rw [complex_rotation_conjugation]
  simp

/-- The real rotation, obtained by taking real coordinates of the complex
weight rotation. -/
def realRotationMap (h : H) : L →ₗ[ℝ] L :=
  (complexificationRealPart L).comp
    ((ComplexCartan.rotationLinear (complexifiedSubalgebra L H)
      (realCartanInComplex L H h)).restrictScalars ℝ |>.comp
      (complexificationLieHom L).toLinearMap)

@[simp] theorem realRotationMap_complexify (h : H) (x : L) :
    (1 : ℂ) ⊗ₜ[ℝ] realRotationMap L H h x =
      ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h)
        (1 ⊗ₜ[ℝ] x) := by
  obtain ⟨y, hy⟩ := exists_real_rotation L H h x
  change (1 : ℂ) ⊗ₜ[ℝ] complexificationRealPart L
    (ComplexCartan.rotationLinear (complexifiedSubalgebra L H) (realCartanInComplex L H h)
      (1 ⊗ₜ[ℝ] x)) = _
  rw [hy, complexificationRealPart_tmul, Complex.one_re, one_smul]

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
@[simp] theorem realCartanInComplex_add (h k : H) :
    realCartanInComplex L H (h + k) = realCartanInComplex L H h + realCartanInComplex L H k := by
  apply Subtype.ext
  simp [realCartanInComplex, TensorProduct.tmul_add]

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] in
@[simp] theorem realCartanInComplex_zero : realCartanInComplex L H 0 = 0 := by
  apply Subtype.ext
  simp [realCartanInComplex]

@[simp] theorem realRotationMap_add_apply (h k : H) (x : L) :
    realRotationMap L H (h + k) x = realRotationMap L H h (realRotationMap L H k x) := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realRotationMap_complexify, realCartanInComplex_add,
    ComplexCartan.rotationLinear_add_apply, realRotationMap_complexify, realRotationMap_complexify]

@[simp] theorem realRotationMap_zero_apply (x : L) : realRotationMap L H 0 x = x := by
  apply complexificationLieHom_injective L
  change (1 : ℂ) ⊗ₜ[ℝ] _ = (1 : ℂ) ⊗ₜ[ℝ] _
  rw [realRotationMap_complexify, realCartanInComplex_zero, ComplexCartan.rotationLinear_zero_apply]

theorem realRotationMap_lie (h : H) (x y : L) :
    realRotationMap L H h ⁅x, y⁆ = ⁅realRotationMap L H h x, realRotationMap L H h y⁆ := by
  apply complexificationLieHom_injective L
  rw [LieHom.map_lie]
  change (1 : ℂ) ⊗ₜ[ℝ] _ = ⁅(1 : ℂ) ⊗ₜ[ℝ] _, (1 : ℂ) ⊗ₜ[ℝ] _⁆
  rw [realRotationMap_complexify, realRotationMap_complexify, realRotationMap_complexify]
  simpa only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] using
    (ComplexCartan.rotationLinear_map_lie (complexifiedSubalgebra L H)
      (realCartanInComplex L H h) ((1 : ℂ) ⊗ₜ[ℝ] x) ((1 : ℂ) ⊗ₜ[ℝ] y))

/-- Removing rotational weights uses actual automorphisms of the original
real Lie algebra, with inverse given by the negative parameter. -/
def realCartanRotation (h : H) : L ≃ₗ⁅ℝ⁆ L where
  toFun := realRotationMap L H h
  map_add' := (realRotationMap L H h).map_add
  map_smul' := (realRotationMap L H h).map_smul
  invFun := realRotationMap L H (-h)
  left_inv x := by rw [← realRotationMap_add_apply, neg_add_cancel, realRotationMap_zero_apply]
  right_inv x := by rw [← realRotationMap_add_apply, add_neg_cancel, realRotationMap_zero_apply]
  map_lie' := fun {x y} => realRotationMap_lie L H h x y

end PolycyclicRecognition

end

end OAI
