import OAI.Geometry.RCD.Transport.CompressedSegmentIntegral

namespace OAI

/-! # Retaining the common full-measure set on selected segments -/

open Set Filter Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_segment_ae (μ : Measure X) (π : Measure C(Time,X)) [SFinite π]
    {C : ℝ≥0∞} (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {Ω : Set X}
    (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ Ω)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ.restrict Ω, P x) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), P (geodesicExtension γ t) := by
  have hlocal (t : Time) : π.map (fun γ => γ t) ≤ C • μ.restrict Ω :=
    (compression_iff_localized μ _ (hstay t) C).mp (hc t)
  have hcomp := testPlanMeasure_compression (μ.restrict Ω) π hlocal
  have heval : ∀ᵐ z ∂testPlanMeasure π, P (testPlanEval z) :=
    ae_of_ae_map testPlanEval_measurable.aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul hcomp).ae_le hP)
  exact Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heval)

end RegularPointCoordinates

end

end OAI
