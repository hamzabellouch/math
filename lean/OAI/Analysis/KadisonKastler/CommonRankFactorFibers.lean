import OAI.Analysis.KadisonKastler.CommonModelFactorFibers
import OAI.Analysis.KadisonKastler.CommonRankSourceModel

namespace OAI

/-! # Factor fibers for a source and its commuting generating source -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

universe u

variable {Z H : Type u} [CommCStarAlgebra Z] [TopologicalSpace.SeparableSpace Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
  [TopologicalSpace.SeparableSpace S] (M : BorelCommonModel π D S.subtype)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankFactorCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
local instance rankFactorCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

omit [TopologicalSpace.SeparableSpace Z] [TopologicalSpace.SeparableSpace S] in
theorem commonRank_factor_fibers
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hAS : A ≤ S) (hCS : C ≤ S)
    (hcomm : ∀ a : A, ∀ c : C, a.val * c.val = c.val * a.val)
    (hgen : representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      starSubalgebraCommutant π.range) (n : ℕ) :
    ∀ᵐ x ∂projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D) n,
      ScalarCenter (commonRankFiberAlgebra M (StarSubalgebra.inclusion hAS) n x) := by
  have hf := commonModel_factor_fibers S M A C hAS hCS hcomm hgen
  have hr := (ae_restrict_iff_subtype (measurableSet_projectionRankStratum
    (commonModelProjection M) (commonRankBasis π D) (commonModelProjection_measurable M) n)).mp
    (ae_restrict_of_ae hf)
  filter_upwards [hr] with x hx
  rw [commonRankFiberAlgebra, representationVonNeumannAlgebra_eq_generated]
  exact fixedFiber_scalarCenter_of_nonunital M.field (commonRankBasis π D) (commonRankBasis_total π D)
    (StarSubalgebra.inclusion hAS) n x hx

end

end KadisonKastler

end OAI
