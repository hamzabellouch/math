import OAI.Analysis.KadisonKastler.L2ProjectionAnalysis
import OAI.Analysis.KadisonKastler.L2PartitionCoordinates
import OAI.Analysis.KadisonKastler.HilbertSumIsometryMap
import OAI.Analysis.KadisonKastler.ProjectionStrataPartition

namespace OAI

/-! # Assembling the fixed-coordinate projection strata -/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  (μ : Measure X) (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
  (hPm : ∀ v, Measurable fun x => P x v)

abbrev projectionStratumMeasure (n : ℕ) : Measure (projectionRankStratum P b n) :=
  Measure.comap ((↑) : projectionRankStratum P b n → X) μ

abbrev ProjectionStrataSpace :=
  lp (fun n => Lp ℓ²(projectionDimensionIndex n, ℂ) 2 (projectionStratumMeasure μ P b n)) 2

def projectionPartitionCoordinates :
    Lp H 2 μ ≃ₗᵢ[ℂ] lp (fun n => Lp H 2 (projectionStratumMeasure μ P b n)) 2 :=
  l2StrataCoordinates μ (projectionRankStratum P b)
    (measurableSet_projectionRankStratum P b hPm)
    (projectionRankStratum_pairwise P b) (iUnion_projectionRankStratum P b)

def projectionStrataSynthesis : ProjectionStrataSpace μ P b →ₗᵢ[ℂ] Lp H 2 μ :=
  (projectionPartitionCoordinates μ P b hPm).symm.toLinearIsometry.comp
    (hilbertSumIsometryMap fun n =>
      l2ProjectionStratumSynthesis P hP b hb hPm n (projectionStratumMeasure μ P b n))

theorem projectionStrataSynthesis_range_components (f : Lp H 2 μ) :
    f ∈ LinearMap.range (projectionStrataSynthesis μ P hP b hb hPm).toLinearMap ↔
      ∀ n, (projectionPartitionCoordinates μ P b hPm f) n ∈
        LinearMap.range (l2ProjectionStratumSynthesis P hP b hb hPm n
          (projectionStratumMeasure μ P b n)).toLinearMap := by
  let e := projectionPartitionCoordinates μ P b hPm
  let S := fun n => l2ProjectionStratumSynthesis P hP b hb hPm n
    (projectionStratumMeasure μ P b n)
  rw [← hilbertSumIsometryMap_range S (e f)]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    change hilbertSumIsometryMap S g = e (e.symm (hilbertSumIsometryMap S g))
    rw [LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply e.injective
    change e (e.symm (hilbertSumIsometryMap S g)) = e f
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hg

theorem projectionStrataSynthesis_range (hPn : ∀ x, ‖P x‖ ≤ 1) (f : Lp H 2 μ) :
    f ∈ LinearMap.range (projectionStrataSynthesis μ P hP b hb hPm).toLinearMap ↔
      ∀ᵐ x ∂μ, P x (f x) = f x := by
  rw [projectionStrataSynthesis_range_components]
  have hc (n : ℕ) : (projectionPartitionCoordinates μ P b hPm f) n =
      l2Restrict μ (projectionRankStratum P b n)
        (measurableSet_projectionRankStratum P b hPm n) f :=
    l2StrataCoordinates_apply μ _ _ _ _ f n
  simp_rw [hc, l2ProjectionStratumSynthesis_range P hP b hb hPm hPn]
  rw [ae_iff_forall_partition μ (projectionRankStratum P b)
    (measurableSet_projectionRankStratum P b hPm) (iUnion_projectionRankStratum P b)]
  constructor <;> intro h n
  · filter_upwards [h n, l2Restrict_apply_ae μ (projectionRankStratum P b n)
      (measurableSet_projectionRankStratum P b hPm n) f] with x hx hr
    rwa [hr] at hx
  · filter_upwards [h n, l2Restrict_apply_ae μ (projectionRankStratum P b n)
      (measurableSet_projectionRankStratum P b hPm n) f] with x hx hr
    rwa [hr]

end

end KadisonKastler

end OAI
