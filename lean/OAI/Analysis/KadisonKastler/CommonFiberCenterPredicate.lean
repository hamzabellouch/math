import OAI.Analysis.KadisonKastler.NonunitalFiberCenter
import OAI.Analysis.KadisonSimilarity.Representation.CommonFiberFactors

namespace OAI

/-! # The common-fiber theorem as a range-center predicate -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

universe u

variable {Z H : Type u} [CommCStarAlgebra Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

theorem ae_common_nonunital_fiber_center
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hcomm : ∀ a : A, ∀ c : C, a.val * c.val = c.val * a.val)
    (hgen : representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      starSubalgebraCommutant π.range)
    (s : Set (WeakDual.characterSpace ℂ Z)) (hs : MeasurableSet s)
    (hnull : (cyclicCommonBaseMeasure π D) sᶜ = 0)
    (ρ : ∀ _x : s, Unitization ℂ (jointCStarSource A C) →⋆ₐ[ℂ]
      (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators))
    (hρ : ∀ a : jointCStarSource A C, ∀ f : CommonCyclicHilbert π D,
      ∀ᵐ x : s ∂Measure.comap Subtype.val (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) a.val f x =
          ρ x (Unitization.inr a) (f x)) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      NonunitalFiberScalarCenter (zeroExtendNonunitalRepresentation s
        (fun y => unitizationRestrict
          (StarSubalgebra.inclusion (le_jointCStarSource_left A C)) (ρ y)) x) :=
  ae_common_fiber_scalar_center π D A C hcomm hgen s hs hnull ρ hρ

end

end KadisonKastler

end OAI
