import OAI.Analysis.KadisonKastler.CommonSpectralMeasurable
import OAI.Analysis.KadisonKastler.FixedFiberFieldAgreement

namespace OAI

/-! # Fixed-rank coordinates for a represented common C-star source

The common spectral model and its Borel representations give a unitary
on each fixed-rank stratum.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {A B H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [CStarAlgebra B] [TopologicalSpace.SeparableSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

local instance rankModelCoordinateMeasurable :
    MeasurableSpace (ScalarHilbertCoordinates D.generators) := borel _
local instance rankModelCoordinateBorel :
    BorelSpace (ScalarHilbertCoordinates D.generators) := ⟨rfl⟩

structure BorelCommonModel (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) where
  field : WeakDual.characterSpace ℂ A → B →⋆ₙₐ[ℂ]
    (ScalarHilbertCoordinates D.generators →L[ℂ] ScalarHilbertCoordinates D.generators)
  measurable : ∀ a v, Measurable fun x => field x a v
  action : ∀ a (f : CommonCyclicHilbert π D),
    isometricExtension (cyclicCommonEmbedding π D) (σ a) f =ᵐ[cyclicCommonBaseMeasure π D]
      fun x => field x a (f x)

def borelCommonModel (σ : B →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hσ : ∀ b a, σ b * π a = π a * σ b) : BorelCommonModel π D σ := by
  let h := exists_measurable_common_representations π D σ hσ
  exact ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2⟩

def commonRankBasis : ℕ → ScalarHilbertCoordinates D.generators :=
  TopologicalSpace.denseSeq _

omit [TopologicalSpace.SeparableSpace A] in
theorem commonRankBasis_total :
    (Submodule.span ℂ (Set.range (commonRankBasis π D))).topologicalClosure = ⊤ := by
  apply SetLike.coe_injective
  change closure (Submodule.span ℂ (Set.range (commonRankBasis π D)) :
    Set (ScalarHilbertCoordinates D.generators)) = Set.univ
  apply Set.eq_univ_of_forall
  intro v
  exact closure_mono Submodule.subset_span (TopologicalSpace.denseRange_denseSeq _ v)

variable {π D} {σ : B →⋆ₐ[ℂ] (H →L[ℂ] H)} (M : BorelCommonModel π D σ)

def commonModelProjection := representationUnitProjection M.field

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_idempotent (x : WeakDual.characterSpace ℂ A) :
    IsIdempotentElem (commonModelProjection M x) :=
  representationUnitProjection_idempotent M.field x

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_norm_le (x : WeakDual.characterSpace ℂ A) :
    ‖commonModelProjection M x‖ ≤ 1 :=
  (nonunitalUnitProjection_isStarProjection (M.field x)).norm_le

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_measurable (v : ScalarHilbertCoordinates D.generators) :
    Measurable fun x => commonModelProjection M x v := M.measurable 1 v

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonModelProjection_action (f : CommonCyclicHilbert π D) :
    isometricExtension (cyclicCommonEmbedding π D) 1 f =ᵐ[cyclicCommonBaseMeasure π D]
      fun x => commonModelProjection M x (f x) := by
  simpa only [map_one, commonModelProjection, representationUnitProjection,
    nonunitalUnitProjection] using M.action (1 : B) f

def commonRankCoordinates : H ≃ₗᵢ[ℂ]
    ProjectionStrataSpace (cyclicCommonBaseMeasure π D) (commonModelProjection M)
      (commonRankBasis π D) :=
  projectionStrataCoordinates (cyclicCommonBaseMeasure π D) (commonModelProjection M)
    (commonModelProjection_idempotent M) (commonRankBasis π D) (commonRankBasis_total π D)
    (commonModelProjection_measurable M) (commonModelProjection_norm_le M)
    (cyclicCommonEmbedding π D) (commonModelProjection_action M)

omit [TopologicalSpace.SeparableSpace A] [TopologicalSpace.SeparableSpace B] in
theorem commonRankCoordinates_action (a : B) (v : H) (n : ℕ) :
    ∀ᵐ x : projectionRankStratum (commonModelProjection M) (commonRankBasis π D) n
      ∂projectionStratumMeasure (cyclicCommonBaseMeasure π D) (commonModelProjection M)
        (commonRankBasis π D) n,
      commonRankCoordinates M (σ a v) n x =
        fixedFiberRepresentation M.field (commonRankBasis π D) (commonRankBasis_total π D)
          n x a (commonRankCoordinates M v n x) := by
  have ha (v : H) : cyclicCommonEmbedding π D (σ a v) =ᵐ[cyclicCommonBaseMeasure π D]
      fun x => M.field x a (cyclicCommonEmbedding π D v x) := by
    simpa only [isometricExtension_on_range] using M.action a (cyclicCommonEmbedding π D v)
  have h := projectionStrataCoordinates_operator_action
    (commonModelProjection M) (commonModelProjection_idempotent M)
    (commonRankBasis π D) (commonRankBasis_total π D) (cyclicCommonBaseMeasure π D)
    (commonModelProjection_measurable M) (commonModelProjection_norm_le M)
    (cyclicCommonEmbedding π D) (commonModelProjection_action M) (σ a)
    (fun x => M.field x a) ha v n
  simpa only [commonRankCoordinates, commonModelProjection,
    compressedStratumField_eq_fixedFiberRepresentation] using h

end

end KadisonKastler

end OAI
