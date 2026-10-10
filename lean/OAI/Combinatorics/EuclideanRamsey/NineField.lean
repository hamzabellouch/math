import OAI.Combinatorics.EuclideanRamsey.NineGeometry
import OAI.Combinatorics.EuclideanRamsey.IndependentTensor
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin

namespace OAI

noncomputable section
open scoped TensorProduct

namespace EuclideanRamsey.NineField

open NineGeometry

abbrev ParameterPoly := IndependentTensor.Poly (Fin 9)
abbrev ParameterField := IndependentTensor.Rat (Fin 9)
abbrev TargetPoly := IndependentTensor.JointPoly (Fin 9)
abbrev TargetField := IndependentTensor.JointField (Fin 9)

/-- The rational scalar structure induced by the fraction-ring construction. -/
local instance parameterFieldAlgebra : Algebra ℚ ParameterField :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := ParameterPoly)
    (S := nonZeroDivisors ParameterPoly)

/-- The rational scalar structure on the joint rational-function field. -/
local instance targetFieldAlgebra : Algebra ℚ TargetField :=
  OreLocalization.instAlgebra (R₀ := ℚ) (R := TargetPoly)
    (S := nonZeroDivisors TargetPoly)

theorem parameterFieldAlgebra_eq_canonical :
    parameterFieldAlgebra = (DivisionRing.toRatAlgebra : Algebra ℚ ParameterField) :=
  Subsingleton.elim _ _

theorem targetFieldAlgebra_eq_canonical :
    targetFieldAlgebra = (DivisionRing.toRatAlgebra : Algebra ℚ TargetField) :=
  Subsingleton.elim _ _

def T (i : Fin 9) : TargetField :=
  algebraMap TargetPoly TargetField (MvPolynomial.X (Sum.inl i))

def U (i : Fin 9) : TargetField :=
  algebraMap TargetPoly TargetField (MvPolynomial.X (Sum.inr i))

/-- The three augmented rational parametrization entries. -/
def a0 : TargetField := 1
def a1 (z : TargetField) : TargetField := (1 - z^2) / (1 + z^2)
def a2 (z : TargetField) : TargetField := (2*z) / (1 + z^2)

def paramVector (z : TargetField) : Option (Fin 2) → TargetField
  | none => a0
  | some j => if j = 0 then a1 z else a2 z

variable (t : Fin 9 → ℝ)

/-- Each parameter is an element of the actual coordinate field, by the
proved recovery formula and coordinate-field equality. -/
def parameter (i : Fin 9) : Coeff (circleConfig t) :=
  ⟨t i, by
    rw [circleConfig_coordinateField]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

@[simp] theorem parameter_coe (i : Fin 9) : (parameter t i : ℝ) = t i := rfl

theorem coordinate_zero (i : Fin 9) :
    coordinate (circleConfig t) i 0 =
      (1 - (parameter t i)^2) / (1 + (parameter t i)^2) := by
  apply Subtype.ext
  simp [coordinate, circleConfig, parameter]

theorem coordinate_one (i : Fin 9) :
    coordinate (circleConfig t) i 1 =
      (2 * parameter t i) / (1 + (parameter t i)^2) := by
  have htwo : ((2 : Coeff (circleConfig t)) : ℝ) = 2 :=
    map_ofNat (coordinateField (circleConfig t)).val 2
  apply Subtype.ext
  simp [coordinate, circleConfig, parameter, htwo]

variable (ht : AlgebraicIndependent ℚ t)

/-- The actual coefficient field is identified with the rational function
field using exactly the given algebraic independence of the real parameters. -/
def coefficientEquiv : Coeff (circleConfig t) ≃ₐ[ℚ] ParameterField :=
  (IntermediateField.equivOfEq (circleConfig_coordinateField t)).trans
    ht.aevalEquivField.symm

@[simp] theorem coefficientEquiv_parameter (i : Fin 9) :
    coefficientEquiv t ht (parameter t i) =
      algebraMap ParameterPoly ParameterField (MvPolynomial.X i) := by
  apply ht.aevalEquivField.injective
  change ht.aevalEquivField
      (ht.aevalEquivField.symm
        ((IntermediateField.equivOfEq (circleConfig_coordinateField t)) (parameter t i))) = _
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  change t i =
    (ht.aevalEquivField
      (algebraMap ParameterPoly ParameterField (MvPolynomial.X i)) : ℝ)
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

def leftCoeff : Coeff (circleConfig t) →ₐ[ℚ] TargetField :=
  (IndependentTensor.leftMap (Fin 9)).comp (coefficientEquiv t ht).toAlgHom

def rightCoeff : Coeff (circleConfig t) →ₐ[ℚ] TargetField :=
  (IndependentTensor.rightMap (Fin 9)).comp (coefficientEquiv t ht).toAlgHom

@[simp] theorem leftCoeff_parameter (i : Fin 9) :
    leftCoeff t ht (parameter t i) = T i := by
  simp [leftCoeff, T]

@[simp] theorem rightCoeff_parameter (i : Fin 9) :
    rightCoeff t ht (parameter t i) = U i := by
  simp [rightCoeff, U]

@[simp] theorem leftCoeff_coordinate_zero (i : Fin 9) :
    leftCoeff t ht (coordinate (circleConfig t) i 0) = a1 (T i) := by
  rw [coordinate_zero]
  simp [a1, map_div₀]

@[simp] theorem leftCoeff_coordinate_one (i : Fin 9) :
    leftCoeff t ht (coordinate (circleConfig t) i 1) = a2 (T i) := by
  rw [coordinate_one]
  simp [a2, map_div₀, map_ofNat]

@[simp] theorem rightCoeff_coordinate_zero (i : Fin 9) :
    rightCoeff t ht (coordinate (circleConfig t) i 0) = a1 (U i) := by
  rw [coordinate_zero]
  simp [a1, map_div₀]

@[simp] theorem rightCoeff_coordinate_one (i : Fin 9) :
    rightCoeff t ht (coordinate (circleConfig t) i 1) = a2 (U i) := by
  rw [coordinate_one]
  simp [a2, map_div₀, map_ofNat]

/-- The tensor equivalence transports both copies of the actual field. -/
def coefficientTensorEquiv :
    TensorRing (circleConfig t) ≃ₐ[ℚ] ParameterField ⊗[ℚ] ParameterField :=
  Algebra.TensorProduct.congr (coefficientEquiv t ht) (coefficientEquiv t ht)

/-- The coordinate-field tensor square embeds in the rational function field
on eighteen variables. -/
def coordinateTensorEmbedding : TensorRing (circleConfig t) →ₐ[ℚ] TargetField :=
  (IndependentTensor.tensorEmbedding (Fin 9)).comp
    (coefficientTensorEquiv t ht).toAlgHom

theorem coordinateTensorEmbedding_injective :
    Function.Injective (coordinateTensorEmbedding t ht) :=
  (IndependentTensor.tensorEmbedding_injective (Fin 9)).comp
    (coefficientTensorEquiv t ht).injective

@[simp] theorem coordinateTensorEmbedding_tmul
    (x y : Coeff (circleConfig t)) :
    coordinateTensorEmbedding t ht (x ⊗ₜ[ℚ] y) =
      leftCoeff t ht x * rightCoeff t ht y := by
  simp [coordinateTensorEmbedding, coefficientTensorEquiv, leftCoeff, rightCoeff]

/-- Exact images of the constant and two spatial augmented coordinates. -/
@[simp] theorem coordinateTensorEmbedding_a0_left (i : Fin 9) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i none) ⊗ₜ[ℚ] 1) = a0 := by
  simp [augmented, a0]

@[simp] theorem coordinateTensorEmbedding_a1_left (i : Fin 9) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i (some 0)) ⊗ₜ[ℚ] 1) = a1 (T i) := by
  simp [augmented]

@[simp] theorem coordinateTensorEmbedding_a2_left (i : Fin 9) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i (some 1)) ⊗ₜ[ℚ] 1) = a2 (T i) := by
  simp [augmented]

@[simp] theorem coordinateTensorEmbedding_a0_right (i : Fin 9) :
    coordinateTensorEmbedding t ht
      (1 ⊗ₜ[ℚ] (augmented (circleConfig t) i none)) = a0 := by
  simp [augmented, a0]

@[simp] theorem coordinateTensorEmbedding_a1_right (i : Fin 9) :
    coordinateTensorEmbedding t ht
      (1 ⊗ₜ[ℚ] (augmented (circleConfig t) i (some 0))) = a1 (U i) := by
  simp [augmented]

@[simp] theorem coordinateTensorEmbedding_a2_right (i : Fin 9) :
    coordinateTensorEmbedding t ht
      (1 ⊗ₜ[ℚ] (augmented (circleConfig t) i (some 1))) = a2 (U i) := by
  simp [augmented]

theorem leftCoeff_augmented (i : Fin 9) (j : Option (Fin 2)) :
    leftCoeff t ht (augmented (circleConfig t) i j) = paramVector (T i) j := by
  cases j with
  | none => simp [augmented, paramVector, a0]
  | some j => fin_cases j <;> simp [augmented, paramVector]

theorem rightCoeff_augmented (i : Fin 9) (j : Option (Fin 2)) :
    rightCoeff t ht (augmented (circleConfig t) i j) = paramVector (U i) j := by
  cases j with
  | none => simp [augmented, paramVector, a0]
  | some j => fin_cases j <;> simp [augmented, paramVector]

/-- The augmented-coordinate tensors map to entries of the rational evaluation matrix. -/
theorem coordinateTensorEmbedding_augmented_tmul (i : Fin 9)
    (α β : Option (Fin 2)) :
    coordinateTensorEmbedding t ht
      ((augmented (circleConfig t) i α) ⊗ₜ[ℚ] (augmented (circleConfig t) i β)) =
      paramVector (T i) α * paramVector (U i) β := by
  rw [coordinateTensorEmbedding_tmul, leftCoeff_augmented, rightCoeff_augmented]

end EuclideanRamsey.NineField

end

end OAI
