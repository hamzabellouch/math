import OAI.Probability.SLE.Geometry.ActualStoppedTubeSupport
import OAI.Probability.SLE.Gauge.RibbonSurvival

namespace OAI

/-! The actual semicircle splice gives conditional passage after a narrow
first-height stop. The physical tube here is in the original parameter
plane, so compact continuation prefixes stay strictly inside the half-plane
and can subsequently be transported through a locally convergent family. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal unitInterval ENNReal

namespace SLEExactGauge

def parameterContinuationRegion (F : ℂ → ℂ) (a : ℂ) (r : ℝ) (O : Set ℂ) : Set ℂ :=
  upperHalfPlane ∩ F ⁻¹' (ball a (r / 2) ∪ O)

theorem parameterContinuationRegion_isOpen
    {F : ℂ → ℂ} (hF : ContinuousOn F upperHalfPlane)
    (a : ℂ) (r : ℝ) {O : Set ℂ} (hO : IsOpen O) :
    IsOpen (parameterContinuationRegion F a r O) :=
  hF.isOpen_inter_preimage isOpen_upperHalfPlane (isOpen_ball.union hO)

theorem exists_physical_splice_route
    (γ : ℝ≥0 → ℂ) (τ : ℝ≥0) {B r tB T : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hheight : (γ τ).im = B / 4) (hx : |(γ τ).re| < B / 16)
    (hpast : γ '' Icc 0 τ ⊆ GuideSplice.closedInitialRectangle B)
    (F : ℂ → ℂ) (a : ℂ) (O : Set ℂ) (β : ℝ → ℂ)
    (htB : 0 < tB) (htBT : tB < T)
    (hβ : ContinuousOn β (Icc 0 T)) (hi : InjOn β (Icc 0 T))
    (hβH : ∀ t ∈ Ioc 0 T, 0 < (β t).im)
    (hcross : ‖β tB‖ = B) (hafter : ∀ t ∈ Ioc tB T, B < ‖β t‖)
    (hcircle : ∀ θ ∈ Ioo 0 Real.pi, ‖F (GuideSplice.circlePoint B θ) - a‖ < r / 4)
    (hsector : ∀ z : ℂ, B / 8 ≤ ‖z‖ → ‖z‖ ≤ B → ‖z‖ / 2 ≤ z.im →
      ‖F z - a‖ < r / 4)
    (htail : F '' (β '' Icc tB T) ⊆ O) :
    ∃ p : Path (γ τ) (β T), Function.Injective p ∧
      (∀ t, t ≠ 0 → p t ∈ survivingDomain γ τ) ∧
      range p ⊆ parameterContinuationRegion F a r O := by
  let x := (γ τ).re
  let ζ : ℂ := (x : ℂ) + ((B / 4 : ℝ) : ℂ) * Complex.I
  have htip : γ τ = ζ := by
    apply Complex.ext <;> simp [ζ, x, hheight]
  have hα : (GuideSplice.connectorTop B x).arg ∈ Ioo 0 Real.pi := by
    apply GuideSplice.arg_mem_upper_interval
    simpa [GuideSplice.connectorTop] using
      Real.sqrt_pos.mpr (GuideSplice.circle_height_pos hB hx)
  have hω : (β tB).arg ∈ Ioo 0 Real.pi :=
    GuideSplice.arg_mem_upper_interval (hβH tB ⟨htB, htBT.le⟩)
  obtain ⟨p, hp, _, hpH, _, hpr⟩ := GuideSplice.exists_simple_splice_path hB hx
    htB htBT hβ hi hβH hcross hafter
  have hrest := GuideSplice.continuationRoute_rest_subset_tube hr hB hx hα hω htB
    hβH hcross hafter hcircle hsector htail
  have hsurv := continuationTube_subset_survivingDomain γ τ B hpast F a r O
  have hpne (t : unitInterval) (ht : t ≠ 0) : p t ≠ ζ := by
    intro he
    apply ht
    apply hp
    simpa only [Path.source] using he
  refine ⟨p.cast htip rfl, hp, ?_, ?_⟩
  · intro t ht
    apply hsurv
    apply hrest
    exact ⟨hpr ▸ mem_range_self t, hpne t ht⟩
  · intro z hz
    refine ⟨hpH hz, ?_⟩
    by_cases he : z = ζ
    · subst z
      have hζV : ζ ∈ GuideSplice.verticalConnector B x := by
        simp only [ζ, GuideSplice.verticalConnector, mem_ofPred_eq, Complex.add_re,
          Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
          Complex.I_im, mul_zero, sub_self, add_zero, Complex.add_im,
          Complex.mul_im, mul_one, zero_add]
        exact ⟨trivial, le_rfl, (GuideSplice.circle_height_gt_quarter hB hx).le⟩
      exact Or.inl (ball_subset_ball (by linarith)
        (GuideSplice.initial_splice_image_subset_quarter_ball hB hx hα hω
          hcircle hsector (mem_image_of_mem F (Or.inl hζV))))
    · exact (hrest ⟨hpr ▸ hz, he⟩).1.2

theorem conditional_stopped_splice_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F₀ : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (G ω) (F₀ ω))
    (hboundary : PublishedLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (B r : ℝ) (hB : 0 < B) (hr : 0 < r) (E : Set Ω)
    (hgeometry : ∀ ω ∈ E, 0 < τ ω ∧ (γ ω (τ ω)).im = B / 4 ∧
      |(γ ω (τ ω)).re| < B / 16 ∧
      (∀ u : ℝ≥0, u < τ ω → (γ ω u).im < (γ ω (τ ω)).im) ∧
      γ ω '' Icc 0 (τ ω) ⊆ GuideSplice.closedInitialRectangle B)
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
    ∀ᵐ ω ∂P, ω ∈ E →
      0 < P⁻[(stoppedPhysicalTube γ τ (parameterContinuationRegion F a r O) W).indicator
        (fun _ => 1) | hτ.measurableSpace] ω := by
  apply conditional_stopped_physical_tube_positive κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw
    hboundary hsupport τ hτ _ W (parameterContinuationRegion_isOpen hF a r hO) hW E
  · intro ω hω
    obtain ⟨hτpos, hh, _, hprior, _⟩ := hgeometry ω hω
    exact ⟨hτpos, by rw [hh]; positivity, hprior⟩
  · intro ω hω
    obtain ⟨_, hh, hx, _, hpast⟩ := hgeometry ω hω
    obtain ⟨p, hp, hpD, hpO⟩ := exists_physical_splice_route (γ ω) (τ ω) hB hr hh hx hpast
      F a O β htB htBT hβ hi hβH hcross hafter hcircle hsector htail
    exact ⟨β T, p, hp, hpD, hpO, hend⟩

end SLEExactGauge

end

end OAI
