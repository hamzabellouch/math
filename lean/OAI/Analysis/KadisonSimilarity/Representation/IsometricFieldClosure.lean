import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyStrongSequence

namespace OAI

/-! Membership in the original represented von Neumann algebra passes to
the fiber algebra through the actual isometric L² embedding. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H F Ω : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace.SeparableSpace F]
  [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Only the source algebra's actual field action and membership are needed;
the fiber fields need not form a simultaneous representation on null sets. -/
theorem ae_field_mem_of_isometric_representation_closure
    (J : H →ₗᵢ[ℂ] Lp F 2 μ) (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (P : Ω → VonNeumannAlgebra F) (R : A → Ω → F →L[ℂ] F)
    (hR : ∀ b (f : Lp F 2 μ), ∀ᵐ x ∂μ,
      isometricExtension J (σ b) f x = R b x (f x))
    (hmem : ∀ b, ∀ᵐ x ∂μ, R b x ∈ P x)
    (T : H →L[ℂ] H) (hT : T ∈ representationVonNeumannAlgebra σ)
    (Q : Ω → F →L[ℂ] F)
    (hQ : ∀ f : Lp F 2 μ, ∀ᵐ x ∂μ, isometricExtension J T f x = Q x (f x)) :
    ∀ᵐ x ∂μ, Q x ∈ P x := by
  obtain ⟨b, hbound, hstrong⟩ := kaplansky_strong_sequence σ T hT
  apply ae_field_mem_of_norm_bounded_strong_approximation μ P
    (fun n => isometricExtension J (σ (b n))) (isometricExtension J T)
    (fun n => R (b n)) Q (fun n => hR (b n)) hQ
    (isometricExtension_strong_tendsto J (fun n => σ (b n)) T hstrong)
    ‖T‖ (norm_nonneg T) ?_ (fun n => hmem (b n))
  intro n
  rw [isometricExtension_norm]
  exact (NonUnitalStarAlgHom.norm_apply_le σ (b n)).trans (hbound n)

end KadisonSimilarity

end

end OAI
