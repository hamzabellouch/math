import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralBilinearLattice

namespace OAI

/-! # Realizing any bilinear integral central extension -/

noncomputable section
namespace PolycyclicRecognition

variable {d e : ℕ}

theorem coefficientBilinear_eq {R : Type*} [CommRing R]
    (β : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin e → R)) :
    coefficientBilinear (fun k i j =>
      β (Pi.basisFun R (Fin d) i) (Pi.basisFun R (Fin d) j) k) = β := by
  apply (Pi.basisFun R (Fin d)).ext
  intro i
  apply (Pi.basisFun R (Fin d)).ext
  intro j
  ext k
  simp [coefficientBilinear, Pi.basisFun_apply, Pi.single_apply]

theorem bilinearIntegral_solvable_realization
    (β : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ) →ₗ[ℤ] (Fin e → ℤ)) :
    ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
      IsUniformLattice Λ ∧ Nonempty (BilinearCentralGroup β ≃* Λ) := by
  have h := integralBilinear_solvable_realization
    (fun k i j => β (Pi.basisFun ℤ (Fin d) i) (Pi.basisFun ℤ (Fin d) j) k)
  rw [coefficientBilinear_eq β] at h
  exact h

end PolycyclicRecognition

end

end OAI
