import OAI.Analysis.KadisonKastler.CommonRankFieldClosure
import OAI.Analysis.KadisonKastler.RepresentationCommutantInclusion
import OAI.Analysis.KadisonKastler.BlockFieldDecomposition
import OAI.Analysis.KadisonKastler.RegularTensorGap
import OAI.Analysis.KadisonKastler.HilbertSumFieldTransport

namespace OAI

/-! # Field decomposition for an algebra and a commuting generating source -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {A B C E H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B] [CStarAlgebra C] [CStarAlgebra E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : A →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

abbrev commonRankMeasure := projectionStratumMeasure (cyclicCommonBaseMeasure π D)
  (commonModelProjection M) (commonRankBasis π D)

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRank_algebra_decompose (ι : C →⋆ₐ[ℂ] B) (P : VonNeumannAlgebra H)
    (hgen : representationVonNeumannAlgebra (σ.comp ι) = P)
    (hcentral : P.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra) :
    ∀ T ∈ spatialTransportAlgebra (commonRankCoordinates M) P,
      ∃ F : ∀ n, projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n →
          ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ),
        (∀ n v, AEStronglyMeasurable (fun x => F n x v) (commonRankMeasure M n)) ∧
        (∀ n, ∀ᵐ x ∂commonRankMeasure M n, ‖F n x‖ ≤ ‖T‖) ∧
        (∀ n, ∀ᵐ x ∂commonRankMeasure M n, F n x ∈ commonRankFiberAlgebra M ι n x) ∧
        ∀ (f : ProjectionStrataSpace (cyclicCommonBaseMeasure π D) (commonModelProjection M)
          (commonRankBasis π D)) n,
          T f n =ᵐ[commonRankMeasure M n] fun x => F n x (f n x) := by
  apply transported_algebra_field_decompose (K := fun n => ℓ²(projectionDimensionIndex n, ℂ))
    (commonRankMeasure M) (commonRankCoordinates M)
    P (commonRankFiberAlgebra M ι)
  intro T hT
  let t : (starSubalgebraCommutant π.range).toStarSubalgebra := ⟨T, hcentral hT⟩
  refine ⟨commonRankOperatorField M t, commonRankOperatorField_aestronglyMeasurable M t,
    ?_, ?_, commonRankOperatorField_action M t⟩
  · intro n
    exact commonRankOperatorField_norm_le M t n
  · intro n
    exact commonRank_field_mem_of_closure M ι t (by rw [hgen]; exact hT) n

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRank_commutant_decompose (ι : C →⋆ₐ[ℂ] B) (κ : E →⋆ₐ[ℂ] B)
    (P : VonNeumannAlgebra H)
    (hgen : representationVonNeumannAlgebra (σ.comp κ) = P.commutant)
    (hcentral : P.commutant.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra)
    (hcomm : ∀ c e, ι c * κ e = κ e * ι c) :
    ∀ T ∈ (spatialTransportAlgebra (commonRankCoordinates M) P).commutant,
      ∃ F : ∀ n, projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n →
          ℓ²(projectionDimensionIndex n, ℂ) →L[ℂ] ℓ²(projectionDimensionIndex n, ℂ),
        (∀ n, ∀ᵐ x ∂commonRankMeasure M n, F n x ∈ (commonRankFiberAlgebra M ι n x).commutant) ∧
        ∀ (f : ProjectionStrataSpace (cyclicCommonBaseMeasure π D) (commonModelProjection M)
          (commonRankBasis π D)) n,
          T f n =ᵐ[commonRankMeasure M n] fun x => F n x (f n x) := by
  exact transported_commutant_fields_of_field_inclusion
    (K := fun n => ℓ²(projectionDimensionIndex n, ℂ)) (commonRankMeasure M)
    (commonRankCoordinates M) P (commonRankFiberAlgebra M ι) (commonRankFiberAlgebra M κ)
    (commonRankFiberAlgebra_le_commutant M ι κ hcomm)
    (commonRank_algebra_decompose M κ P.commutant hgen hcentral)

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRank_algebra_decomposition (ι : C →⋆ₐ[ℂ] B) (κ : E →⋆ₐ[ℂ] B)
    (P : VonNeumannAlgebra H)
    (hgen : representationVonNeumannAlgebra (σ.comp ι) = P)
    (hgen' : representationVonNeumannAlgebra (σ.comp κ) = P.commutant)
    (hcentral : P.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra)
    (hcentral' : P.commutant.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra)
    (hcomm : ∀ c e, ι c * κ e = κ e * ι c) :
    ∃ Q : ∀ n, VonNeumannAlgebra (Lp ℓ²(projectionDimensionIndex n, ℂ) 2 (commonRankMeasure M n)),
      BlockAlgebraDecomposition Q (spatialTransportAlgebra (commonRankCoordinates M) P) ∧
      ∀ n, OperatorFieldDecomposition (commonRankMeasure M n) (commonRankFiberAlgebra M ι n) (Q n) := by
  exact exists_block_field_decomposition (K := fun n => ℓ²(projectionDimensionIndex n, ℂ))
    (commonRankMeasure M)
    (spatialTransportAlgebra (commonRankCoordinates M) P) (commonRankFiberAlgebra M ι)
    (commonRank_algebra_decompose M ι P hgen hcentral)
    (commonRank_commutant_decompose M ι κ P hgen' hcentral' hcomm)

end

end KadisonKastler

end OAI
