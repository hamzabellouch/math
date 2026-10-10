import OAI.Analysis.KadisonKastler.LiftedRankStrata
import OAI.Analysis.KadisonKastler.CommonRankSourceModel
import OAI.Analysis.KadisonKastler.FieldCoordinateTransport
import OAI.Analysis.KadisonKastler.SpatialCoordinateComposition

namespace OAI

/-! # The fixed-coordinate algebra fields after the universe lift -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

universe u

variable {A B C H : Type u} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B] [CStarAlgebra C]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

omit [TopologicalSpace.SeparableSpace B] in
theorem liftedRankFiberAlgebra_eq (ι : C →⋆ₐ[ℂ] B) (n : ℕ) (x : (commonRankStratum M n).X) :
    spatialTransportAlgebra (rankFiberLift n) (commonRankFiberAlgebra M ι n x) =
      generatedVonNeumannAlgebra ((liftedRankRepresentation M n x).comp ι).range := by
  change spatialTransportAlgebra (rankFiberLift n)
    (representationVonNeumannAlgebra ((fixedFiberRepresentation M.field
      (commonRankBasis π D) (commonRankBasis_total π D) n x).comp ι)) = _
  rw [spatialTransport_representation, representationVonNeumannAlgebra_eq_generated]
  rfl

omit [TopologicalSpace.SeparableSpace B] in
theorem liftedRank_field_decomposition (ι : C →⋆ₐ[ℂ] B) (n : ℕ)
    (Q : VonNeumannAlgebra (Lp ℓ²(projectionDimensionIndex n, ℂ) 2 (commonRankSourceMeasure M n)))
    (hQ : OperatorFieldDecomposition (commonRankSourceMeasure M n) (commonRankFiberAlgebra M ι n) Q) :
    OperatorFieldDecomposition (commonRankStratum M n).μ
      (fun x => generatedVonNeumannAlgebra ((liftedRankRepresentation M n x).comp ι).range)
      (spatialTransportAlgebra (commonRankStratumEquiv M n) Q) := by
  change OperatorFieldDecomposition (commonRankSourceMeasure M n)
    (fun x => generatedVonNeumannAlgebra ((liftedRankRepresentation M n x).comp ι).range)
    (spatialTransportAlgebra
      (l2CoordinateEquiv (commonRankSourceMeasure M n) (rankFiberLift n)) Q)
  have h := operatorFieldDecomposition_coordinate_transport (commonRankSourceMeasure M n)
    (rankFiberLift n) (commonRankFiberAlgebra M ι n) Q hQ
  have he : (fun x : (commonRankStratum M n).X =>
      spatialTransportAlgebra (rankFiberLift n) (commonRankFiberAlgebra M ι n x)) =
      (fun x => generatedVonNeumannAlgebra ((liftedRankRepresentation M n x).comp ι).range) :=
    funext (fun x => liftedRankFiberAlgebra_eq M ι n x)
  exact he ▸ h

omit [TopologicalSpace.SeparableSpace B] in
theorem liftedRank_scalarCenter (ι : C →⋆ₐ[ℂ] B) (n : ℕ) (x : (commonRankStratum M n).X)
    (h : ScalarCenter (commonRankFiberAlgebra M ι n x)) :
    ScalarCenter (generatedVonNeumannAlgebra ((liftedRankRepresentation M n x).comp ι).range) := by
  rw [← liftedRankFiberAlgebra_eq]
  exact ScalarCenter.spatialTransport (rankFiberLift n) _ h

end

end KadisonKastler

end OAI
