import OAI.Analysis.IrrationalRotation.Spectral.PolarOrbitInvariance
import OAI.Analysis.IrrationalRotation.Operators.AtomicNonscalarProjection
import OAI.Analysis.IrrationalRotation.Operators.ProjectionAtomOrbit

namespace OAI

noncomputable section
namespace Invariant233.PolarOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem fullPolarAlgebra_isDiffuse_of_periodic_projections
    (U : unitary (H →L[ℂ] H)) (B : H →L[ℂ] H)
    (N : VonNeumannAlgebra H) (ξ : H)
    (hU : (U : H →L[ℂ] H) ∈ N) (hB : B ∈ N)
    (hξ : IsFaithfulTracialVector N ξ)
    (hab : IsAbelianVonNeumannAlgebra (fullPolarAlgebra (U : H →L[ℂ] H) B))
    (hatomic : HasCountablyAtomicSpectralType B)
    (hnonscalar : ¬ ∃ c : ℂ, B = c • (1 : H →L[ℂ] H))
    (htotal : ∀ n : ℕ, 0 < n → ∀ p : H →L[ℂ] H,
      p ∈ fullPolarAlgebra (U : H →L[ℂ] H) B → IsStarProjection p →
      (U : H →L[ℂ] H) ^ n * p * star (U : H →L[ℂ] H) ^ n = p →
      p = 0 ∨ p = 1) :
    IsDiffuseVonNeumannAlgebra (fullPolarAlgebra (U : H →L[ℂ] H) B) := by
  have hMN := fullPolarAlgebra_le (U : H →L[ℂ] H) B N hU hB
  apply ProjectionAtomOrbit.isDiffuse_of_total_ergodicity ξ
    (fun A hA C hC => hab A C hA hC)
    (ProjectionAtomOrbit.faithfulTracialVector_restrict hMN ξ hξ)
    (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) U)
  · exact fun A => fullPolarAlgebra_mem_iff U B A
  · intro A hA
    exact ProjectionAtomOrbit.vectorTrace_unitary_conjugation ξ hξ U hU (hMN hA)
  · intro n hn p hp hproj hperiod
    apply htotal n hn p hp hproj
    rw [iterate_conjStarAlgAut] at hperiod
    simpa only [Unitary.conjStarAlgAut_apply, SubmonoidClass.coe_pow, star_pow] using hperiod
  · exact exists_nontrivial_projection_of_atomic_nonscalar _ B
      (mem_fullPolarAlgebra (U : H →L[ℂ] H) B) hatomic hnonscalar

end Invariant233.PolarOrbit

end

end OAI
