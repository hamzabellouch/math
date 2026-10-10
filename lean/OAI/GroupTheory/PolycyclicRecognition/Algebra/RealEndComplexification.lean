import OAI.GroupTheory.PolycyclicRecognition.Algebra.SpectralConjugation
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

/-! # Complexifying real matrices and their semisimple parts

This is the concrete finite-dimensional scalar extension used in the real
matrix logarithm. No abstract real-form theory is needed.
-/

noncomputable section
namespace PolycyclicRecognition

variable (n : ℕ)

def realEndComplexification :
    Module.End ℝ (Fin n → ℝ) →ₐ[ℝ] Module.End ℂ (Fin n → ℂ) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ]
    Module.End ℂ (Fin n → ℂ)).restrictScalars ℝ).toAlgHom.comp
      (((Algebra.ofId ℝ ℂ).mapMatrix).comp
        (LinearMap.toMatrixAlgEquiv' : Module.End ℝ (Fin n → ℝ) ≃ₐ[ℝ]
          Matrix (Fin n) (Fin n) ℝ).toAlgHom)

theorem realEndComplexification_apply (A : Module.End ℝ (Fin n → ℝ))
    (x : Fin n → ℂ) (i : Fin n) :
    realEndComplexification n A x i =
      ∑ j, (A (Pi.single j 1) i : ℂ) * x j := rfl

theorem realEndComplexification_matrix (A : Module.End ℝ (Fin n → ℝ)) :
    LinearMap.toMatrixAlgEquiv' (realEndComplexification n A) =
      (LinearMap.toMatrixAlgEquiv' A).map Complex.ofReal := by
  exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _

theorem realEndComplexification_conj (A : Module.End ℝ (Fin n → ℝ))
    (x : Fin n → ℂ) :
    star (realEndComplexification n A x) = realEndComplexification n A (star x) := by
  ext i
  simp [realEndComplexification_apply, star_sum, star_mul, mul_comm]

theorem realEndComplexification_semisimple (A : Module.End ℝ (Fin n → ℝ))
    (hA : A.IsSemisimple) : (realEndComplexification n A).IsSemisimple := by
  let p := (minpoly ℝ A).map (algebraMap ℝ ℂ)
  have hp : Squarefree p :=
    (PerfectField.separable_iff_squarefree.mpr hA.minpoly_squarefree).map.squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  have he := Polynomial.map_aeval_eq_aeval_map
    (φ := algebraMap ℝ ℂ) (ψ := (realEndComplexification n).toRingHom)
    (by
      apply RingHom.ext
      intro r
      exact ((realEndComplexification n).commutes r).symm)
    (minpoly ℝ A) A
  rw [minpoly.aeval, map_zero] at he
  exact he.symm

end PolycyclicRecognition

end

end OAI
