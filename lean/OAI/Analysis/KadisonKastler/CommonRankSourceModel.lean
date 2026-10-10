import OAI.Analysis.KadisonKastler.CommonRankOperatorFields
import OAI.Analysis.KadisonKastler.HilbertSumFieldClosure
import OAI.Analysis.KadisonKastler.RepresentationCommutantInclusion

namespace OAI

/-! # Actual rank fields of a represented bicommutant member

Kaplansky approximation on the original representation, transported through
the constructed unitary, places the rank fields in the corresponding fiber
bicommutants. The common source may be larger than the algebra being closed.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

abbrev CommonRankSpace := ProjectionStrataSpace (H := ScalarHilbertCoordinates D.generators)
  (cyclicCommonBaseMeasure π D)
  (commonModelProjection M) (commonRankBasis π D)

abbrev commonRankSourceMeasure := projectionStratumMeasure
  (H := ScalarHilbertCoordinates D.generators) (cyclicCommonBaseMeasure π D)
  (commonModelProjection M) (commonRankBasis π D)

def commonRankFiberAlgebra {C : Type*} [CStarAlgebra C] (ι : C →⋆ₐ[ℂ] B)
    (n : ℕ) (x : projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n) :
    VonNeumannAlgebra ℓ²(projectionDimensionIndex n, ℂ) :=
  representationVonNeumannAlgebra ((fixedFiberRepresentation M.field (commonRankBasis π D)
    (commonRankBasis_total π D) n x).comp ι)

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonRankFiberAlgebra_le_commutant
    {C E : Type*} [CStarAlgebra C] [CStarAlgebra E]
    (ι : C →⋆ₐ[ℂ] B) (κ : E →⋆ₐ[ℂ] B)
    (hcomm : ∀ c e, ι c * κ e = κ e * ι c)
    (n : ℕ) (x : projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n) :
    commonRankFiberAlgebra M κ n x ≤ (commonRankFiberAlgebra M ι n x).commutant :=
  representation_compositions_le_commutant
    (fixedFiberRepresentation M.field (commonRankBasis π D) (commonRankBasis_total π D) n x)
    ι κ hcomm

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonRankSpace_separable : TopologicalSpace.SeparableSpace (CommonRankSpace M) :=
  DenseRange.separableSpace (α := H) (β := CommonRankSpace M)
    (f := commonRankCoordinates M) (commonRankCoordinates M).surjective.denseRange
    (commonRankCoordinates M).continuous

end

end KadisonKastler

end OAI
