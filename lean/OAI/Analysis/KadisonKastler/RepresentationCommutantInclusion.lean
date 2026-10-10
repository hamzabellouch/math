import OAI.Analysis.KadisonSimilarity.Representation.RepresentationCenterTransport
import OAI.Analysis.KadisonKastler.PublishedKaplansky

namespace OAI

/-! # Bicommutants of commuting source representations -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem representationVonNeumannAlgebra_eq_generated
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    representationVonNeumannAlgebra σ = generatedVonNeumannAlgebra σ.range := by
  apply SetLike.coe_injective
  rw [coe_representationVonNeumannAlgebra, generatedVonNeumannAlgebra_coe]

theorem representation_le_commutant_of_commutes
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (τ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : ∀ a b, σ a * τ b = τ b * σ a) :
    representationVonNeumannAlgebra τ ≤ (representationVonNeumannAlgebra σ).commutant := by
  intro T hT
  apply (mem_representation_commutant_iff σ T).mpr
  rintro _ ⟨a, rfl⟩
  have ha : σ a ∈ starSubalgebraCommutant τ.range := by
    rw [← SetLike.mem_coe, coe_starSubalgebraCommutant]
    rintro _ ⟨b, rfl⟩
    exact (h a b).symm
  exact VonNeumannAlgebra.mem_commutant_iff.mp hT (σ a) ha

theorem representation_compositions_le_commutant
    {C : Type*} [CStarAlgebra C]
    (ρ : C →⋆ₐ[ℂ] (H →L[ℂ] H)) (ι : A →⋆ₐ[ℂ] C) (κ : B →⋆ₐ[ℂ] C)
    (h : ∀ a b, ι a * κ b = κ b * ι a) :
    representationVonNeumannAlgebra (ρ.comp κ) ≤
      (representationVonNeumannAlgebra (ρ.comp ι)).commutant := by
  apply representation_le_commutant_of_commutes
  intro a b
  simpa only [StarAlgHom.comp_apply, map_mul] using congrArg ρ (h a b)

end

end KadisonKastler

end OAI
