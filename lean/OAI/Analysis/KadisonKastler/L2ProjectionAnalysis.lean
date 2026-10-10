import OAI.Analysis.KadisonKastler.L2ProjectionSynthesis

namespace OAI

/-! # Recovering the L² sections of a projection field

On each rank stratum the synthesis range consists exactly of the sections
fixed by the original projection field.
-/

namespace KadisonKastler

open MeasureTheory
open scoped lp

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  (P : X → H →L[ℂ] H) (hP : ∀ x, IsIdempotentElem (P x))
  (b : ℕ → H) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
  (hPm : ∀ v, Measurable fun x => P x v) (hPn : ∀ x, ‖P x‖ ≤ 1)

local instance coordinateMeasurable (n : ℕ) : MeasurableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  borel _
local instance coordinateBorel (n : ℕ) : BorelSpace ℓ²(projectionDimensionIndex n, ℂ) := ⟨rfl⟩
local instance coordinateSeparable (n : ℕ) :
    TopologicalSpace.SeparableSpace ℓ²(projectionDimensionIndex n, ℂ) :=
  separable_scalarHilbertCoordinates

omit [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H]
  [TopologicalSpace.SeparableSpace H] in
include hPn in
theorem projectionStratumAnalysis_norm_le (n : ℕ) (x : projectionRankStratum P b n) :
    ‖projectionStratumAnalysis P hP b hb n x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  exact (projectionStratumAnalysis_apply_norm_le P hP b hb n x v).trans
    (mul_le_mul_of_nonneg_right (hPn x.val) (norm_nonneg v))

def l2ProjectionStratumAnalysis (n : ℕ) (μ : Measure (projectionRankStratum P b n)) :
    Lp H 2 μ →L[ℂ] Lp ℓ²(projectionDimensionIndex n, ℂ) 2 μ :=
  l2LinearFieldMap μ (projectionStratumAnalysis P hP b hb n)
    (fun v => (projectionStratumAnalysis_measurable P hP b hb hPm n v).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall (projectionStratumAnalysis_norm_le P hP b hb hPn n))

theorem l2ProjectionStratumAnalysis_ae (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) (f : Lp H 2 μ) :
    l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f =ᵐ[μ]
      fun x => projectionStratumAnalysis P hP b hb n x (f x) :=
  l2LinearFieldApply_ae μ _
    (fun v => (projectionStratumAnalysis_measurable P hP b hb hPm n v).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall (projectionStratumAnalysis_norm_le P hP b hb hPn n)) f

theorem l2Projection_synthesis_analysis (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) (f : Lp H 2 μ) :
    l2ProjectionStratumSynthesis P hP b hb hPm n μ
      (l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f) =ᵐ[μ]
        fun x => P x.val (f x) := by
  filter_upwards [l2ProjectionStratumSynthesis_ae P hP b hb hPm n μ
      (l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f),
    l2ProjectionStratumAnalysis_ae P hP b hb hPm hPn n μ f] with x hs ha
  rw [hs, ha, projectionStratumSynthesis_analysis]

theorem l2Projection_analysis_synthesis (n : ℕ)
    (μ : Measure (projectionRankStratum P b n))
    (f : Lp ℓ²(projectionDimensionIndex n, ℂ) 2 μ) :
    l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ
      (l2ProjectionStratumSynthesis P hP b hb hPm n μ f) = f := by
  apply Lp.ext
  filter_upwards [l2ProjectionStratumAnalysis_ae P hP b hb hPm hPn n μ
      (l2ProjectionStratumSynthesis P hP b hb hPm n μ f),
    l2ProjectionStratumSynthesis_ae P hP b hb hPm n μ f] with x ha hs
  rw [ha, hs, projectionStratumAnalysis_synthesis]

include hPn in
theorem l2ProjectionStratumSynthesis_range (n : ℕ)
    (μ : Measure (projectionRankStratum P b n)) (f : Lp H 2 μ) :
    f ∈ LinearMap.range (l2ProjectionStratumSynthesis P hP b hb hPm n μ).toLinearMap ↔
      ∀ᵐ x ∂μ, P x.val (f x) = f x := by
  constructor
  · rintro ⟨g, rfl⟩
    filter_upwards [l2ProjectionStratumSynthesis_ae P hP b hb hPm n μ g] with x hx
    change P x.val (l2ProjectionStratumSynthesis P hP b hb hPm n μ g x) =
      l2ProjectionStratumSynthesis P hP b hb hPm n μ g x
    rw [hx, projectionStratumSynthesis_fixed]
  · intro hf
    refine ⟨l2ProjectionStratumAnalysis P hP b hb hPm hPn n μ f, ?_⟩
    exact Lp.ext ((l2Projection_synthesis_analysis P hP b hb hPm hPn n μ f).trans hf)

end

end KadisonKastler

end OAI
