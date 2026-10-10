import OAI.Analysis.KadisonSimilarity.Representation.CommonCommutantFields
import OAI.Analysis.KadisonSimilarity.Representation.ProjectionCentralData

namespace OAI

/-! The common spectral model supplies the actual central-decomposition
data for a weakly generating separable source. Factoriality is proved
separately using the joint source. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

universe u
variable {A H : Type u} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- All operators commuting with the center acquire fields in the single
common spectral model. -/
def commonCentralField (P : VonNeumannAlgebra H)
    (hcentral : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant)
    (T : (vonNeumannCenter P).commutant.toStarSubalgebra) :
    WeakDual.characterSpace ℂ A → ScalarHilbertCoordinates D.generators →L[ℂ]
      ScalarHilbertCoordinates D.generators :=
  commonCommutantField π D ⟨T.val, by rw [hcentral]; exact T.property⟩

theorem commonCentralField_action (P : VonNeumannAlgebra H)
    (hcentral : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant)
    (T : (vonNeumannCenter P).commutant.toStarSubalgebra) (f : CommonCyclicHilbert π D) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      isometricExtension (cyclicCommonEmbedding π D) T f x =
        commonCentralField π D P hcentral T x (f x) :=
  commonCommutantField_action π D
    ⟨T.val, by rw [hcentral]; exact T.property⟩ f

/-- Central decomposition with all scalar/matrix norms and countable
contraction tests derived from the common spectral embedding. -/
def commonProjectionCentralData (P : VonNeumannAlgebra H)
    (B : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (B : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace B]
    (hB : B ≤ P.toStarSubalgebra)
    (hBgen : representationVonNeumannAlgebra B.subtype = P)
    (hcentral : starSubalgebraCommutant π.range = (vonNeumannCenter P).commutant)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ B →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ b : B, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
          ρ x (Unitization.inr b) (f x)) :
    CentralDecompositionData (cyclicCommonBaseMeasure π D) (conullProjectionFiber s ρ) P :=
  projectionCentralData (cyclicCommonBaseMeasure π D) P B hB hBgen s hs hnull
    (cyclicCommonEmbedding π D) ρ hρ (commonCentralField π D P hcentral)
    (commonCentralField_action π D P hcentral)

end KadisonSimilarity

end

end OAI
