import OAI.Analysis.KadisonSimilarity.FreeProduct.CommonFieldCompression
import OAI.Analysis.KadisonSimilarity.Representation.SupportedRankOneMembership
import OAI.Analysis.KadisonSimilarity.Representation.ScalarHilbertSeparability

namespace OAI

/-! Supported rank-one fields belong to the joint fiber bicommutant when
the source generates the original central commutant. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {A B H : Type u} [CommCStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- Every compressed constant rank-one field lies almost everywhere in the
fiber bicommutant. Its original operator is constructed by compression. -/
theorem ae_common_projection_rankOne_mem
    (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hgen : representationVonNeumannAlgebra σ = starSubalgebraCommutant π.range)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ b : B, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (σ b) f x =
          ρ x (Unitization.inr b) (f x))
    (v w : ScalarHilbertCoordinates D.generators) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      InnerProductSpace.rankOne ℂ
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) v)
        (projectionFiberRetraction
          (nonunitalUnitProjection (zeroExtendNonunitalRepresentation s ρ x))
          (nonunitalUnitProjection_isStarProjection (zeroExtendNonunitalRepresentation s ρ x)) w) ∈
        representationVonNeumannAlgebra
          (nonunitalRangeRepresentation (zeroExtendNonunitalRepresentation s ρ x)) := by
  exact ae_supported_projection_rankOne_mem (cyclicCommonBaseMeasure π D)
    (cyclicCommonEmbedding π D) σ s hs hnull ρ hρ
    (commonFieldCompression_mem_of_range_eq π D σ hgen) v w

end KadisonSimilarity

end

end OAI
