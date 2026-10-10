import OAI.Analysis.KadisonKastler.CentralVectorMatrixLimit

namespace OAI

/-! # Conjugation and central-vector projections -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem starProjection_conjugate (K : Submodule ℂ H) [CompleteSpace K]
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hK : ∀ ξ ∈ K, J ξ ∈ K) (ξ : H) :
    K.starProjection (J ξ) = J (K.starProjection ξ) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hK _ (K.starProjection_apply_mem ξ))
  intro w hw
  rw [← map_sub J]
  have hi := conjugateIsometry_inner J (ξ - K.starProjection ξ) (J w)
  rw [hJ w] at hi
  rw [hi,K.starProjection_inner_eq_zero ξ (J w) (hK w hw),star_zero]

theorem matrixCentralVectorSpace_conjugate {M : VonNeumannAlgebra H}
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) {ξ : H} (hξ : ξ ∈ matrixCentralVectorSpace A J) :
    J ξ ∈ matrixCentralVectorSpace A J := by
  apply (Submodule.mem_iInf _).mpr
  intro n
  exact centralVectorSpace_conjugate _ J hJ (matrixCentralVectorSpace_le A J n hξ)

theorem matrixCentralVectorSpace_projection_fixed {M : VonNeumannAlgebra H}
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (ξ : H) (hξ : J ξ = ξ) :
    J ((matrixCentralVectorSpace A J).starProjection ξ) =
      (matrixCentralVectorSpace A J).starProjection ξ := by
  rw [← starProjection_conjugate _ J hJ (fun _ h => matrixCentralVectorSpace_conjugate A J hJ h),hξ]

end

end KadisonKastler

end OAI
