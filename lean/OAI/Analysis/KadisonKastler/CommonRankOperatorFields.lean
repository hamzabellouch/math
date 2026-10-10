import OAI.Analysis.KadisonKastler.CommonRankCoordinates
import OAI.Analysis.KadisonKastler.HilbertSumFieldAction

namespace OAI

/-! # Fields of all central-commutant operators in the rank coordinates -/

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

local instance rankFieldCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
local instance rankFieldCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

def commonRankOperatorField
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) (n : ℕ) :=
  compressedStratumField (commonModelProjection M) (commonModelProjection_idempotent M)
    (commonRankBasis π D) (commonRankBasis_total π D) (commonCommutantField π D T) n

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRankOperatorField_action
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra)
    (f : ProjectionStrataSpace (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D)) (n : ℕ) :
    ((commonRankCoordinates M).conjStarAlgEquiv T f) n =ᵐ[
      projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
        (commonRankBasis π D) n]
      fun x => commonRankOperatorField M T n x (f n x) := by
  have ha (v : H) : cyclicCommonEmbedding π D (T.val v) =ᵐ[cyclicCommonBaseMeasure π D]
      fun x => commonCommutantField π D T x (cyclicCommonEmbedding π D v x) := by
    change ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      cyclicCommonEmbedding π D (T.val v) x =
        commonCommutantField π D T x (cyclicCommonEmbedding π D v x)
    simpa only [isometricExtension_on_range] using
      commonCommutantField_action π D T (cyclicCommonEmbedding π D v)
  have h := projectionStrataCoordinates_operator_action
    (commonModelProjection M) (commonModelProjection_idempotent M)
    (commonRankBasis π D) (commonRankBasis_total π D) (cyclicCommonBaseMeasure π D)
    (commonModelProjection_measurable M) (commonModelProjection_norm_le M)
    (cyclicCommonEmbedding π D) (commonModelProjection_action M) T.val
    (commonCommutantField π D T) ha ((commonRankCoordinates M).symm f) n
  change (commonRankCoordinates M (T.val ((commonRankCoordinates M).symm f))) n =ᵐ[_]
    fun x => commonRankOperatorField M T n x (f n x)
  change (commonRankCoordinates M (T.val ((commonRankCoordinates M).symm f))) n =ᵐ[_]
    fun x => commonRankOperatorField M T n x
      ((commonRankCoordinates M ((commonRankCoordinates M).symm f)) n x) at h
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRankOperatorField_aestronglyMeasurable
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) (n : ℕ)
    (v : ℓ²(projectionDimensionIndex n, ℂ)) :
    AEStronglyMeasurable (fun x => commonRankOperatorField M T n x v)
      (projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
        (commonRankBasis π D) n) := by
  apply compressedStratumField_aestronglyMeasurable _ _ _ _
    (commonModelProjection_measurable M)
  intro w
  have hc := pointwise_action_column (cyclicCommonBaseMeasure π D) _ _
    (commonCommutantField_action π D T) w
  have hm := (Lp.aestronglyMeasurable _).congr hc
  exact hm.restrict.comp_measurePreserving
    (measurePreserving_subtype_coe (μa := cyclicCommonBaseMeasure π D)
      (measurableSet_projectionRankStratum (commonModelProjection M)
        (commonRankBasis π D) (commonModelProjection_measurable M) n))

omit [TopologicalSpace.SeparableSpace B] in
theorem commonRankOperatorField_norm_le
    (T : (starSubalgebraCommutant π.range).toStarSubalgebra) (n : ℕ) :
    ∀ᵐ x ∂projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D) n, ‖commonRankOperatorField M T n x‖ ≤ ‖T.val‖ := by
  have hn := (commonCommutantField_norm_iff π D T ‖T.val‖ (norm_nonneg _)).mp le_rfl
  have hr := (ae_restrict_iff_subtype
    (measurableSet_projectionRankStratum (commonModelProjection M)
      (commonRankBasis π D) (commonModelProjection_measurable M) n)).mp
    (ae_restrict_of_ae hn)
  filter_upwards [hr] with x hx
  exact (compressedStratumField_norm_le _ _ _ _ (commonModelProjection_norm_le M)
    (commonCommutantField π D T) n x).trans hx

end

end KadisonKastler

end OAI
