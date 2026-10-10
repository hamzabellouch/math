import OAI.Analysis.KadisonKastler.LiftedRankAlgebras
import OAI.Analysis.KadisonKastler.CommonRankAlgebraFields

namespace OAI

/-! # Packaging the constructed rank model as the exact central-pair data -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

universe u

variable {H Z : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [CommCStarAlgebra Z] [TopologicalSpace.SeparableSpace Z]
  {π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

omit [TopologicalSpace.SeparableSpace H] in
theorem sourceInclusion_comp {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {A C S : StarSubalgebra ℂ (H →L[ℂ] H)}
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    [IsClosed (S : Set (H →L[ℂ] H))]
    (ρ : S →⋆ₐ[ℂ] (K →L[ℂ] K)) (hAC : A ≤ C) (hCS : C ≤ S) :
    (ρ.comp (StarSubalgebra.inclusion hCS)).comp (StarSubalgebra.inclusion hAC) =
      ρ.comp (StarSubalgebra.inclusion (hAC.trans hCS)) := by
  apply StarAlgHom.ext
  intro a
  rfl

theorem centralPairDecomposition_of_rankModel
    (M N : VonNeumannAlgebra H) (A B C S : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (B : Set (H →L[ℂ] H))]
    [IsClosed (C : Set (H →L[ℂ] H))] [IsClosed (S : Set (H →L[ℂ] H))]
    [TopologicalSpace.SeparableSpace S]
    (model : BorelCommonModel π D S.subtype)
    (hAC : A ≤ C) (hBC : B ≤ C) (hCS : C ≤ S)
    (Q R : ∀ n, VonNeumannAlgebra (Lp ℓ²(projectionDimensionIndex n, ℂ) 2
      (commonRankSourceMeasure model n)))
    (hQ : BlockAlgebraDecomposition Q (spatialTransportAlgebra (commonRankCoordinates model) M))
    (hR : BlockAlgebraDecomposition R (spatialTransportAlgebra (commonRankCoordinates model) N))
    (hQf : ∀ n, OperatorFieldDecomposition (commonRankSourceMeasure model n)
      (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hAC.trans hCS)) n) (Q n))
    (hRf : ∀ n, OperatorFieldDecomposition (commonRankSourceMeasure model n)
      (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hBC.trans hCS)) n) (R n))
    (hf : ∀ n, ∀ᵐ x ∂commonRankSourceMeasure model n,
      ScalarCenter (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hAC.trans hCS)) n x) ∧
      ScalarCenter (commonRankFiberAlgebra model (StarSubalgebra.inclusion (hBC.trans hCS)) n x)) :
    Nonempty (CentralPairDecomposition M N A B C hAC hBC) := by
  refine ⟨{
    stratum := commonRankStratum model
    coordinates := liftedRankCoordinates model
    leftBlock := fun n => spatialTransportAlgebra (commonRankStratumEquiv model n) (Q n)
    rightBlock := fun n => spatialTransportAlgebra (commonRankStratumEquiv model n) (R n)
    leftBlocks := ?_
    rightBlocks := ?_
    representation := fun n x => (liftedRankRepresentation model n x).comp (StarSubalgebra.inclusion hCS)
    representation_measurable := ?_
    leftFields := ?_
    rightFields := ?_
    factors := ?_ }⟩
  · have h := blockAlgebraDecomposition_coordinate_transport (commonRankStratumEquiv model)
      Q (spatialTransportAlgebra (commonRankCoordinates model) M) hQ
    rw [spatialTransportAlgebra_trans] at h
    exact h
  · have h := blockAlgebraDecomposition_coordinate_transport (commonRankStratumEquiv model)
      R (spatialTransportAlgebra (commonRankCoordinates model) N) hR
    rw [spatialTransportAlgebra_trans] at h
    exact h
  · intro n c v
    exact liftedRankRepresentation_measurable model n (StarSubalgebra.inclusion hCS c) v
  · intro n
    have h := liftedRank_field_decomposition model (StarSubalgebra.inclusion (hAC.trans hCS))
      n (Q n) (hQf n)
    simpa only [sourceInclusion_comp] using h
  · intro n
    have h := liftedRank_field_decomposition model (StarSubalgebra.inclusion (hBC.trans hCS))
      n (R n) (hRf n)
    simpa only [sourceInclusion_comp] using h
  · intro n
    filter_upwards [hf n] with x hx
    constructor
    · simpa only [sourceInclusion_comp] using
        liftedRank_scalarCenter model (StarSubalgebra.inclusion (hAC.trans hCS)) n x hx.1
    · simpa only [sourceInclusion_comp] using
        liftedRank_scalarCenter model (StarSubalgebra.inclusion (hBC.trans hCS)) n x hx.2

end

end KadisonKastler

end OAI
