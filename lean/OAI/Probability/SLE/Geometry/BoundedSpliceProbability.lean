import OAI.Probability.SLE.Gauge.StoppedSplicePassage
import OAI.Probability.SLE.Geometry.FirstHeightBounded

namespace OAI

/-! Passage from the actual bounded first-height event. The geometry of
the stopped past is derived from the measurable certificate, rather than
imposed separately on the stopped Loewner realization. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem brownian_capacity_trace_adapted
    {Ω : Type*} [m : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (κ : ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) :
    Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => γ ω t) := by
  apply capacity_trace_adapted _ (fun t ω => Real.sqrt κ * B t ω) _
    (fun ω => continuous_const.mul (hc ω)) γ G F hw
  intro t
  exact measurable_const.mul
    ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) t).measurable

theorem bounded_firstHeight_splice_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F₀ : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (G ω) (F₀ ω))
    (hboundary : PublishedLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (B r : ℝ) (hB : 0 < B) (hr : 0 < r) (Tc : ℝ≥0)
    (F : ℂ → ℂ) (hF : ContinuousOn F upperHalfPlane) (a : ℂ)
    (O W : Set ℂ) (hO : IsOpen O) (hW : IsOpen W)
    (β : ℝ → ℂ) (tB T : ℝ) (htB : 0 < tB) (htBT : tB < T)
    (hβ : ContinuousOn β (Icc 0 T)) (hi : InjOn β (Icc 0 T))
    (hβH : ∀ t ∈ Ioc 0 T, 0 < (β t).im)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖)
    (hcircle : ∀ θ ∈ Ioo 0 Real.pi, ‖F (GuideSplice.circlePoint B θ) - a‖ < r / 4)
    (hsector : ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
      ‖F z - a‖ < r / 4)
    (htail : F '' (β '' Icc tB T) ⊆ O) (hend : β T ∈ W) :
    let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
    let σ := fun ω => FirstHeightSupport.boundedFirstHeightTime (γ ω) B Tc
    let hσ := FirstHeightSupport.boundedFirstHeightTime_isStoppingTime ℱ γ
      (brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw) (fun ω => (hw ω).1) B Tc
    ∀ᵐ ω ∂P, ω ∈ FirstHeightSupport.stoppedNarrowCertificate γ σ B Tc →
      0 < P⁻[(stoppedPhysicalTube γ σ (parameterContinuationRegion F a r O) W).indicator
        (fun _ => 1) | hσ.measurableSpace] ω := by
  dsimp only
  let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
  let σ := fun ω => FirstHeightSupport.boundedFirstHeightTime (γ ω) B Tc
  have hσ := FirstHeightSupport.boundedFirstHeightTime_isStoppingTime ℱ γ
    (brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw) (fun ω => (hw ω).1) B Tc
  apply conditional_stopped_splice_positive κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw
    hboundary hsupport σ hσ B r hB hr
    (FirstHeightSupport.stoppedNarrowCertificate γ σ B Tc) _
    F hF a O W hO hW β tB T htB htBT hβ hi hβH hcross hafter hcircle hsector htail hend
  intro ω hω
  exact (FirstHeightSupport.bounded_certificate_geometry
    (sourceTracePath γ (fun ω => (hw ω).1) ω)
    (hw ω).2.1 (hw ω).2.2.1 hB Tc hω).2

/-- Actual bounded-height splice support combined with varying early events
produces one positive probability for the whole sequence of charts. -/
theorem bounded_firstHeight_splice_varying_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F₀ : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (G ω) (F₀ ω))
    (hboundary : PublishedLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (B r : ℝ) (hB : 0 < B) (hr : 0 < r) (Tc : ℝ≥0)
    (F : ℂ → ℂ) (hF : ContinuousOn F upperHalfPlane) (a : ℂ)
    (O W : Set ℂ) (hO : IsOpen O) (hW : IsOpen W)
    (β : ℝ → ℂ) (tB T : ℝ) (htB : 0 < tB) (htBT : tB < T)
    (hβ : ContinuousOn β (Icc 0 T)) (hi : InjOn β (Icc 0 T))
    (hβH : ∀ t ∈ Ioc 0 T, 0 < (β t).im)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖)
    (hcircle : ∀ θ ∈ Ioo 0 Real.pi, ‖F (GuideSplice.circlePoint B θ) - a‖ < r / 4)
    (hsector : ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
      ‖F z - a‖ < r / 4)
    (htail : F '' (β '' Icc tB T) ⊆ O) (hend : β T ∈ W) :
    let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
    let σ := fun ω => FirstHeightSupport.boundedFirstHeightTime (γ ω) B Tc
    let hσ := FirstHeightSupport.boundedFirstHeightTime_isStoppingTime ℱ γ
      (brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw) (fun ω => (hw ω).1) B Tc
    let E := FirstHeightSupport.stoppedNarrowCertificate γ σ B Tc
    let C := stoppedPhysicalTube γ σ (parameterContinuationRegion F a r O) W
    ∀ H : ℕ → Set Ω, (∀ n, MeasurableSet[hσ.measurableSpace] (H n)) →
      0 < P E → (∀ n, P (E \ H n) ≤ P E / 2) →
      ∃ q : ℝ≥0∞, 0 < q ∧ ∀ n, q ≤ P (E ∩ H n ∩ C) := by
  dsimp only
  let : IsProbabilityMeasure P := hB₀.isGaussianProcess.isProbabilityMeasure
  let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
  let σ := fun ω => FirstHeightSupport.boundedFirstHeightTime (γ ω) B Tc
  have ha := brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw
  have hσ := FirstHeightSupport.boundedFirstHeightTime_isStoppingTime ℱ γ ha
    (fun ω => (hw ω).1) B Tc
  let E := FirstHeightSupport.stoppedNarrowCertificate γ σ B Tc
  let C := stoppedPhysicalTube γ σ (parameterContinuationRegion F a r O) W
  intro H hH hEpos hmissing
  have hE : MeasurableSet[hσ.measurableSpace] E :=
    FirstHeightSupport.boundedFirstHeight_certificate_measurable ℱ γ ha
      (fun ω => (hw ω).1) B Tc
  have hγm (t : ℝ≥0) : Measurable (fun ω => γ ω t) :=
    (ha t).mono (ℱ.le t) le_rfl
  have hC : MeasurableSet C := measurableSet_stoppedPhysicalTube γ
    (fun ω => (hw ω).1) hγm σ (stopping_time_measurable_nnreal hσ)
    (parameterContinuationRegion F a r O) W
    (parameterContinuationRegion_isOpen hF a r hO) hW
  have hpass := bounded_firstHeight_splice_positive κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw
    hboundary hsupport B r hB hr Tc F hF a O W hO hW β tB T htB htBT hβ hi hβH
    hcross hafter hcircle hsector htail hend
  exact varying_passage_events_lower_bound P hσ.measurableSpace hσ.measurableSpace_le
    E C H hE hC hH hEpos hpass hmissing

end SLEExactGauge

end

end OAI
