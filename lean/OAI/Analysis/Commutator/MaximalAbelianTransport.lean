import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {A H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

lemma range_of_maximal_conjugate (U : H ≃ₗᵢ[ℂ] G) (σ : A → (H →L[ℂ] H)) (ρ : A → (G →L[ℂ] G))
    (hρ : Set.centralizer (Set.range ρ)=Set.range ρ)
    (hU : ∀ a,U.conjStarAlgEquiv (σ a)=ρ a)
    (T : H →L[ℂ] H) (hT : ∀ a,Commute (σ a) T) : ∃ a,σ a=T := by
  have ht : U.conjStarAlgEquiv T∈Set.centralizer (Set.range ρ) := by
    rintro _ ⟨a,rfl⟩
    rw [←hU,←map_mul,←map_mul]
    exact congrArg U.conjStarAlgEquiv (hT a).eq
  rw [hρ] at ht
  obtain ⟨a,ha⟩ := ht
  exact ⟨a,U.conjStarAlgEquiv.injective ((hU a).trans ha)⟩

end Kadison

end

end
end

end OAI
