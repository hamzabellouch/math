import OAI.Geometry.RCD.Transport.LocalizedPlanEnergy
import Mathlib.MeasureTheory.Integral.Average

namespace OAI

/-! # Integrating a local defect along a compressed geodesic plan

This is the first-moment step for the functional almost-splitting argument.
It retains the full local integrable defect, and permits the selected segment
to avoid any additional null set of paths.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem compressed_segment_integral
    (μ : Measure X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {Ω : Set X}
    (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ Ω)
    {F : X → ℝ} (hF : IntegrableOn F Ω μ)
    (hFpos : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ F x) :
    Integrable (fun γ : C(Time,X) =>
      ∫ t in Icc (0:ℝ) 1, F (geodesicExtension γ t)) π ∧
    (∀ᵐ γ ∂π, IntegrableOn (fun t => F (geodesicExtension γ t)) (Icc (0:ℝ) 1)) ∧
    (∫ γ : C(Time,X), (∫ t in Icc (0:ℝ) 1,
      F (geodesicExtension γ t)) ∂π) ≤ C.toReal * ∫ x in Ω, F x ∂μ := by
  have hlocal (t : Time) : π.map (fun γ => γ t) ≤ C • μ.restrict Ω :=
    (compression_iff_localized μ _ (hstay t) C).mp (hc t)
  have hcomp := testPlanMeasure_compression (μ.restrict Ω) π hlocal
  have hmap := Integrable.of_measure_le_smul hC hcomp hF
  have hprod := hmap.comp_measurable testPlanEval_measurable
  have hbound : (∫ z, F (testPlanEval z) ∂testPlanMeasure π) ≤
      C.toReal * ∫ x in Ω, F x ∂μ := by
    rw [← integral_map testPlanEval_measurable.aemeasurable hmap.aestronglyMeasurable]
    simpa only [integral_smul_measure,smul_eq_mul] using
      integral_mono_measure hcomp (Measure.ae_smul_measure hFpos C) (hF.smul_measure hC)
  refine ⟨hprod.integral_prod_right,hprod.prod_left_ae,?_⟩
  exact (integral_prod_symm _ hprod).symm.le.trans hbound

theorem exists_compressed_segment
    (μ : Measure X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hc : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {Ω : Set X}
    (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ Ω)
    {F : X → ℝ} (hF : IntegrableOn F Ω μ)
    (hFpos : ∀ᵐ x ∂μ.restrict Ω, 0 ≤ F x)
    {P : C(Time,X) → Prop} (hP : ∀ᵐ γ ∂π, P γ) :
    ∃ γ : C(Time,X), P γ ∧
      IntegrableOn (fun t => F (geodesicExtension γ t)) (Icc (0:ℝ) 1) ∧
      (∫ t in Icc (0:ℝ) 1, F (geodesicExtension γ t)) ≤
        C.toReal * ∫ x in Ω, F x ∂μ := by
  obtain ⟨hi,hinner,hbound⟩ := compressed_segment_integral μ π hC hc hstay hF hFpos
  obtain ⟨γ,hγ,havg⟩ := exists_notMem_null_le_integral hi (ae_iff.mp (hP.and hinner))
  exact ⟨γ,(of_not_not hγ).1,(of_not_not hγ).2,havg.trans hbound⟩

end RegularPointCoordinates

end

end OAI
