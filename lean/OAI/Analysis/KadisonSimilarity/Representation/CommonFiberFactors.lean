import OAI.Analysis.KadisonSimilarity.Representation.CommonRankOneClosure
import OAI.Analysis.KadisonSimilarity.Representation.GlobalFiberRestriction
import OAI.Analysis.KadisonSimilarity.Representation.RepresentationCenterTransport
import OAI.Analysis.KadisonSimilarity.Representation.JointFiberFactorCriterion

namespace OAI

/-! The common joint source gives factor fibers for the first algebra,
using countably many compressed constant rank-one tests. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter

universe u
variable {A H : Type u} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

/-- The first source's genuine range fibers have scalar center almost
everywhere when the joint source generates the central commutant. -/
theorem ae_common_fiber_scalar_center
    (B C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (B : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hBC : ∀ b : B, ∀ c : C, (b : H →L[ℂ] H) * (c : H →L[ℂ] H) =
      (c : H →L[ℂ] H) * (b : H →L[ℂ] H))
    (hgen : representationVonNeumannAlgebra (jointCStarSource B C).subtype =
      starSubalgebraCommutant π.range)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource B C) →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ b : jointCStarSource B C, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap ((↑) : s → WeakDual.characterSpace ℂ A)
        (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) (b : H →L[ℂ] H) f x =
          ρ x (Unitization.inr b) (f x)) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      ∀ a : (representationVonNeumannAlgebra (nonunitalRangeRepresentation
        (zeroExtendNonunitalRepresentation s
          (fun y => unitizationRestrict
            (StarSubalgebra.inclusion (le_jointCStarSource_left B C)) (ρ y)) x))).toStarSubalgebra,
        (∀ b, a * b = b * a) → ∃ c : ℂ, a = algebraMap ℂ _ c := by
  apply ae_joint_fiber_scalar_center B C hBC (cyclicCommonBaseMeasure π D) s ρ
    (TopologicalSpace.denseSeq (ScalarHilbertCoordinates D.generators))
    (TopologicalSpace.denseRange_denseSeq (ScalarHilbertCoordinates D.generators))
  intro i j
  exact ae_common_projection_rankOne_mem π D (jointCStarSource B C).subtype
    hgen s hs hnull ρ hρ _ _

end KadisonSimilarity

end

end OAI
