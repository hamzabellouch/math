import OAI.Analysis.KadisonKastler.ProjectionStrataSynthesis
import OAI.Analysis.KadisonKastler.IsometryRangeCoordinates

namespace OAI

/-! # Unitary coordinates for the original spectral subspace

The original isometric embedding and the assembled measurable rank strata
have the same range. Their comparison is the required genuine unitary.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped lp

noncomputable section

variable {X H E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (μ : Measure X) (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
  (hPm : ∀ v, Measurable fun x => P x v)

theorem projectionStrataSynthesis_restrict (f : ProjectionStrataSpace μ P b) (n : ℕ) :
    l2Restrict μ (projectionRankStratum P b n)
        (measurableSet_projectionRankStratum P b hPm n)
        (projectionStrataSynthesis μ P hP b hb hPm f) =
      l2ProjectionStratumSynthesis P hP b hb hPm n (projectionStratumMeasure μ P b n) (f n) := by
  rw [← l2StrataCoordinates_apply μ (projectionRankStratum P b)
    (measurableSet_projectionRankStratum P b hPm)
    (projectionRankStratum_pairwise P b) (iUnion_projectionRankStratum P b)]
  change (projectionPartitionCoordinates μ P b hPm
    ((projectionPartitionCoordinates μ P b hPm).symm (hilbertSumIsometryMap _ f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

variable (hPn : ∀ x, ‖P x‖ ≤ 1) (J : E →ₗᵢ[ℂ] Lp H 2 μ)
  (hJ : ∀ f : Lp H 2 μ, isometricExtension J 1 f =ᵐ[μ] fun x => P x (f x))

def projectionStrataCoordinates : E ≃ₗᵢ[ℂ] ProjectionStrataSpace μ P b :=
  isometryRangeCoordinates J (projectionStrataSynthesis μ P hP b hb hPm) (by
    ext f
    rw [isometry_range_iff_field_fixed μ J P hJ,
      projectionStrataSynthesis_range μ P hP b hb hPm hPn])

theorem projectionStrataCoordinates_intertwines (v : E) :
    projectionStrataSynthesis μ P hP b hb hPm
      (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v) = J v :=
  isometryRangeCoordinates_intertwines J _ _ v

theorem projectionStrataCoordinates_fiber_ae (v : E) (n : ℕ) :
    ∀ᵐ x : projectionRankStratum P b n ∂projectionStratumMeasure μ P b n,
      projectionStratumSynthesis P hP b hb n x
        (projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v n x) = J v x.val := by
  let f := projectionStrataCoordinates μ P hP b hb hPm hPn J hJ v
  have hr := projectionStrataSynthesis_restrict μ P hP b hb hPm f n
  rw [projectionStrataCoordinates_intertwines] at hr
  filter_upwards [l2ProjectionStratumSynthesis_ae P hP b hb hPm n
      (projectionStratumMeasure μ P b n) (f n),
    l2Restrict_apply_ae μ (projectionRankStratum P b n)
      (measurableSet_projectionRankStratum P b hPm n) (J v)] with x hs hx
  exact hs.symm.trans ((congrArg (fun g => g x) hr).symm.trans hx)

end

end KadisonKastler

end OAI
