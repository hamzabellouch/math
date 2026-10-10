import OAI.Analysis.KadisonSimilarity.Tracial.NormalTracialGeometry

namespace OAI

/-! An actual unitary intertwiner transports normality of a represented range. -/

noncomputable section
namespace KadisonSimilarity

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem normal_range_of_unitary_intertwining
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (U : H ≃ₗᵢ[ℂ] K) (hU : ∀ a, U.conjStarAlgEquiv (σ a) = ρ a)
    (N : VonNeumannAlgebra K) (hρ : ρ.range = N.toStarSubalgebra) :
    σ.range = (representationVonNeumannAlgebra σ).toStarSubalgebra := by
  ext T
  constructor
  · rintro ⟨a, rfl⟩
    exact mem_representationVonNeumannAlgebra σ a
  · intro hT
    let θ := U.conjStarAlgEquiv
    have hTN : θ T ∈ N := by
      change T ∈ representationVonNeumannAlgebra σ at hT
      rw [← SetLike.mem_coe, coe_representationVonNeumannAlgebra] at hT
      rw [← SetLike.mem_coe, ← N.centralizer_centralizer]
      intro c hc
      apply θ.symm.injective
      simp only [map_mul]
      change θ.symm c * θ.symm (θ T) = θ.symm (θ T) * θ.symm c
      rw [θ.symm_apply_apply]
      apply hT (θ.symm c)
      rintro _ ⟨a, rfl⟩
      apply θ.injective
      simp only [map_mul]
      change θ (σ a) * θ (θ.symm c) = θ (θ.symm c) * θ (σ a)
      rw [θ.apply_symm_apply, hU]
      apply hc
      change ρ a ∈ N.toStarSubalgebra
      rw [← hρ]
      exact ⟨a, rfl⟩
    have hTr : θ T ∈ ρ.range := by
      rw [hρ]
      exact hTN
    obtain ⟨a, ha⟩ := hTr
    exact ⟨a, θ.injective ((hU a).trans ha)⟩

end KadisonSimilarity

end

end OAI
