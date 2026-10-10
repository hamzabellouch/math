import OAI.Analysis.KadisonSimilarity.Representation.CommonSpectralCommutant
import OAI.Analysis.KadisonSimilarity.Representation.DiagonalFiberRepresentations
import OAI.Analysis.KadisonSimilarity.Representation.UnitizationProjection
import OAI.Analysis.KadisonSimilarity.Representation.ConullRepresentationExtension
import OAI.Analysis.KadisonSimilarity.Representation.ScalarHilbertSeparability

namespace OAI

/-! Genuine representations of a norm-separable algebra on the fibers of
the common spectral model. The old unit supplies the projection onto the
fibers of the original Hilbert space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- Every commuting norm-separable algebra has genuine unital fiber
representations after adjoining the ambient identity. -/
theorem exists_conull_common_representations
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) :
    ∃ s : Set (WeakDual.characterSpace ℂ A), MeasurableSet s ∧
      (cyclicCommonBaseMeasure π D) sᶜ = 0 ∧
      ∃ ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ]
          (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators),
        ∀ (b : B) (f : CommonCyclicHilbert π D),
          ∀ᵐ (x : s) ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
              (cyclicCommonBaseMeasure π D),
            isometricExtension (cyclicCommonEmbedding π D) (σ b) f x =
              ρ x (Unitization.inr b) (f x) := by
  let : TopologicalSpace.SeparableSpace (Unitization ℂ B) := separable_unitization
  obtain ⟨s, hsm, hsnull, ρ, haction, _⟩ :=
    exists_conull_diagonal_star_representations (cyclicCommonBaseMeasure π D)
      (unitalizedExtension (cyclicCommonEmbedding π D) σ) (by
        intro b r hr
        apply unitalizedExtension_commutes
        intro c
        exact commonExtension_commutes_localizations π D (σ c) (hσ c) r hr)
  refine ⟨s, hsm, hsnull, ρ, ?_⟩
  intro b f
  simpa only [unitalizedExtension_inr] using haction (Unitization.inr b) f

/-- Extending the conull representation by zero gives genuine nonunital
representations at every point, retaining the action of the original algebra. -/
theorem exists_common_nonunital_representations
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) :
    ∃ ρ : WeakDual.characterSpace ℂ A → B →⋆ₙₐ[ℂ]
        (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators),
      ∀ (b : B) (f : CommonCyclicHilbert π D),
        ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
          isometricExtension (cyclicCommonEmbedding π D) (σ b) f x = ρ x b (f x) := by
  obtain ⟨s, hsm, hsnull, ρ, haction⟩ := exists_conull_common_representations π D σ hσ
  refine ⟨zeroExtendNonunitalRepresentation s ρ, ?_⟩
  intro b f
  have h := zeroExtendOperatorField_action (cyclicCommonBaseMeasure π D) s hsm hsnull
    (isometricExtension (cyclicCommonEmbedding π D) (σ b))
    (fun y => ρ y (Unitization.inr b)) (haction b) f
  simpa only [zeroExtendNonunitalRepresentation_apply] using h

end KadisonSimilarity

end

end OAI
