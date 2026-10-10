import OAI.Probability.SLE.Geometry.BoundedSpliceProbability
import OAI.Probability.SLE.Gauge.FirstFrontPassage
import OAI.Probability.SLE.Geometry.UniformAccessLocalization

namespace OAI

/-! Sequencewise ribbon passage from the actual bounded first-height event.
The early event is stopped-image containment, and the retained mass window is
the actual first front crossing constructed from the continuation. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.SequencePassage
open FirstHeightSupport EarlyPassageLocalization FirstFrontPassage

/-- The actual stopped-image events give one positive splice probability.
The finite initial part of the sequence does not need an early-loss estimate. -/
theorem eventual_bounded_splice_probability
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
    (htail : F '' (β '' Icc tB T) ⊆ O) (hend : β T ∈ W)
    (Fbar : ℕ → ℂ → OnePoint ℂ)
    (hbar : ∀ n, ContinuousOn (Fbar n) closedHalfPlane)
    (aₙ : ℕ → ℂ) (ρ : ℝ)
    (hpositive : 0 < P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc))
    (hmissing : ∀ᶠ n in atTop, P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc \
        stoppedImageEvent γ (fun ω => boundedFirstHeightTime (γ ω) B Tc)
          (Fbar n) (aₙ n) ρ) ≤
      P (stoppedNarrowCertificate γ (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc) / 2) :
    ∃ q : ℝ, 0 < q ∧ ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P
      (stoppedImageEvent γ (fun ω => boundedFirstHeightTime (γ ω) B Tc)
        (Fbar n) (aₙ n) ρ ∩
       (stoppedNarrowCertificate γ (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc ∩
        stoppedPhysicalTube γ (fun ω => boundedFirstHeightTime (γ ω) B Tc)
          (parameterContinuationRegion F a r O) W)) := by
  classical
  let : IsProbabilityMeasure P := hB₀.isGaussianProcess.isProbabilityMeasure
  let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
  let σ := fun ω => boundedFirstHeightTime (γ ω) B Tc
  have ha := brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw
  have hσ := boundedFirstHeightTime_isStoppingTime ℱ γ ha (fun ω => (hw ω).1) B Tc
  let E := stoppedNarrowCertificate γ σ B Tc
  let H : ℕ → Set Ω := fun n => stoppedImageEvent γ σ (Fbar n) (aₙ n) ρ
  let C := stoppedPhysicalTube γ σ (parameterContinuationRegion F a r O) W
  have hH : ∀ n, MeasurableSet[hσ.measurableSpace] (H n) := fun n =>
    stoppedImageEvent_measurable ℱ γ ha (fun ω => (hw ω).1)
      (fun ω t => (hw ω).2.2.1 t) σ hσ Tc
      (fun ω => boundedFirstHeightTime_le (γ ω) B Tc) (Fbar n) (hbar n) (aₙ n) ρ
  let H' : ℕ → Set Ω := fun n => if P (E \ H n) ≤ P E / 2 then H n else univ
  have hH' : ∀ n, MeasurableSet[hσ.measurableSpace] (H' n) := by
    intro n
    dsimp only [H']
    split_ifs
    · exact hH n
    · exact MeasurableSet.univ
  have hmiss : ∀ n, P (E \ H' n) ≤ P E / 2 := by
    intro n
    dsimp only [H']
    split_ifs with hn
    · exact hn
    · simp only [sdiff_univ, measure_empty, zero_le]
  obtain ⟨q, hq, hqH⟩ := bounded_firstHeight_splice_varying_probability
    κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw hboundary hsupport B r hB hr Tc
    F hF a O W hO hW β tB T htB htBT hβ hi hβH hcross hafter hcircle hsector htail hend
    H' hH' hpositive hmiss
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top P _) (hqH 0)
  refine ⟨q.toReal, ENNReal.toReal_pos hq.ne' hqtop, ?_⟩
  filter_upwards [hmissing] with n hn
  have heq : H' n = H n := ite_eq_left hn
  rw [ENNReal.ofReal_toReal hqtop]
  have hh := hqH n
  rw [heq] at hh
  exact hh.trans (measure_mono (fun _ hω => ⟨hω.1.2, hω.1.1, hω.2⟩))

/-- The published support input and proved scaling law give a real positive
lower probability, uniformly in the first-height scale. -/
theorem uniform_bounded_firstHeight_real_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F₀ : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (G ω) (F₀ ω))
    (hsupport : PublishedGeometricTubeSupport P γ) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ q : ℝ, 0 < q ∧ ∀ B : ℝ, 0 < B →
      ENNReal.ofReal q ≤ P (stoppedNarrowCertificate γ
        (fun ω => boundedFirstHeightTime (γ ω) B (T₀ * (Real.toNNReal B) ^ 2))
        B (T₀ * (Real.toNNReal B) ^ 2)) := by
  let : IsProbabilityMeasure P := hB₀.isGaussianProcess.isProbabilityMeasure
  obtain ⟨T₀, hT₀, q, hq, hprob⟩ := uniform_boundedFirstHeight_probability
    κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw hsupport
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top P _) (hprob 1 zero_lt_one)
  refine ⟨T₀, hT₀, q.toReal, ENNReal.toReal_pos hq.ne' hqtop, ?_⟩
  intro B hB
  have hh := hprob (Real.toNNReal B) (Real.toNNReal_pos.mpr hB)
  simpa only [ENNReal.ofReal_toReal hqtop, Real.coe_toNNReal B hB.le] using hh

end SLEExactGauge.SequencePassage

end

end OAI
