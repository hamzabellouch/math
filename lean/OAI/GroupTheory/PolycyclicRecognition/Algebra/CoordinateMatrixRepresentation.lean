import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothCoordinateAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraHomLieDifferential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FaithfulDifferential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialOneParameterNilpotent
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! # Matrix representations from finite-dimensional coordinate orbits -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff Matrix.Norms.Operator
attribute [local instance 100] LieRing.ofAssociativeRing

variable {G I : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [Group G] [LieGroup (𝓘(ℝ, G)) ⊤ G] {m : ℕ}
  (q : I → G → ℝ) (B : (Fin m → ℝ) ≃ₗ[ℝ] coordinateOrbitSpan q)

def coordinateMatrixRepresentation : G →* Matrix.GeneralLinearGroup (Fin m) ℝ :=
  (Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom).comp
    (smoothCoordinateAction q B).asGroupHom

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem coordinateMatrixRepresentation_injective
    (hq : Function.Injective (fun g => fun i => q i g)) :
    Function.Injective (coordinateMatrixRepresentation q B) := by
  intro x y h
  have hA := LinearMap.toMatrixAlgEquiv'.injective (congrArg Units.val h)
  apply coordinateOrbitRepresentation_injective q hq
  exact B.symm.conjRingEquiv.injective hA

omit [FiniteDimensional ℝ G] in
theorem contDiff_coordinateMatrixRepresentation (hq : ∀ i, ContDiff ℝ ∞ (q i)) :
    ContDiff ℝ ∞ (fun g => (coordinateMatrixRepresentation q B g : Matrix (Fin m) (Fin m) ℝ)) := by
  let e : (Fin m → Fin m → ℝ) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ := LinearEquiv.refl ℝ _
  have hf : ContDiff ℝ ∞ (fun g => fun i j => smoothCoordinateAction q B g (Pi.single j 1) i) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_pi.mp (contDiff_smoothCoordinateAction q B hq (Pi.single j 1)) i
  exact e.toContinuousLinearEquiv.contDiff.comp hf

def coordinateMatrixDifferential (hq : ∀ i, ContDiff ℝ ∞ (q i)) :
    GroupLieAlgebra (𝓘(ℝ, G)) G →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℝ :=
  unitsHomLieDifferential (coordinateMatrixRepresentation q B)
    (contDiff_coordinateMatrixRepresentation q B hq).contMDiff

theorem coordinateMatrixDifferential_injective (hq : ∀ i, ContDiff ℝ ∞ (q i))
    (hi : Function.Injective (fun g => fun i => q i g)) :
    Function.Injective (coordinateMatrixDifferential q B hq) :=
  injective_algebra_differential groupExponential_isGroupExponential
    (coordinateMatrixRepresentation q B) (coordinateMatrixRepresentation_injective q B hi)
    (coordinateMatrixDifferential q B hq).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (coordinateMatrixRepresentation q B)
      (contDiff_coordinateMatrixRepresentation q B hq).contMDiff)

theorem coordinateMatrixDifferential_exp (hq : ∀ i, ContDiff ℝ ∞ (q i))
    (v : GroupLieAlgebra (𝓘(ℝ, G)) G) :
    coordinateMatrixRepresentation q B (groupExponential v) =
      algebraExpUnit (coordinateMatrixDifferential q B hq v) :=
  hom_exp_eq_algebraExpUnit groupExponential_isGroupExponential
    (coordinateMatrixRepresentation q B) (coordinateMatrixDifferential q B hq).toLinearMap.toContinuousLinearMap
    (hasMFDerivAt_unitsHomLieDifferential (coordinateMatrixRepresentation q B)
      (contDiff_coordinateMatrixRepresentation q B hq).contMDiff) v

theorem coordinateMatrixDifferential_nilpotent (hq : ∀ i, ContDiff ℝ ∞ (q i))
    (v : GroupLieAlgebra (𝓘(ℝ, G)) G)
    (hγ : ∀ a b i, (fun t : ℝ => q i ((a * groupExponential (t • v)) * b)) ∈ polynomialFunctions) :
    IsNilpotent (coordinateMatrixDifferential q B hq v) := by
  let A := coordinateMatrixDifferential q B hq v
  let f : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun t => (coordinateMatrixRepresentation q B (groupExponential (t • v)) : Matrix (Fin m) (Fin m) ℝ)
  have hf0 : f 0 = 1 := by simp [f, groupExponential_isGroupExponential.map_zero]
  have hadd (s t : ℝ) : f (s + t) = f s * f t := by
    dsimp [f]
    rw [groupExponential_isGroupExponential.map_add_smul, map_mul]
    rfl
  have heq : f = fun t => NormedSpace.exp (t • A) := by
    funext t
    have h := congrArg Units.val (coordinateMatrixDifferential_exp q B hq (t • v))
    simp only [coe_algebraExpUnit, map_smul] at h
    exact h
  have hzero : HasDerivAt f A 0 := by
    rw [heq]
    let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h := hasDerivAt_exp_smul_const A (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  apply isNilpotent_of_polynomial_oneParameter hf0 hadd hzero
  intro i j
  exact mem_polynomialFunctions_iff.mp
    (polynomial_smoothCoordinateAction q B _ hγ (Pi.single j 1) (LinearMap.proj i))

end PolycyclicRecognition

end

end OAI
