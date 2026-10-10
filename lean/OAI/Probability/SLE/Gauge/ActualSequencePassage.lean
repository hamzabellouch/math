import OAI.Probability.SLE.Geometry.ActualGuideCompactness
import OAI.Probability.SLE.Gauge.SequencePassageSuccess

namespace OAI

/-! The actual joint guide compactness theorem retains the whole normalized
parameter-guide family. Uniform convergence of that family supplies the
common access point and the small physical radius needed by the proved
sequence passage theorem. No separate access-radius hypothesis is needed. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.SequencePassage
open FirstHeightSupport EarlyPassageLocalization FirstFrontPassage PassageSuccess

/-- Uniform guide convergence and simplicity of the limiting guide give a
nonzero common access point at an arbitrarily small positive guide time. -/
theorem small_initial_access_segment
    (C : ℝ≥0) (r : ℝ) (hr : 0 < r)
    (βₙ : ℕ → ℝ → ℂ) (β : ℝ → ℂ)
    (hβ0 : β 0 = 0) (hβi : InjOn β (Icc 0 2))
    (hconv : TendstoUniformlyOn βₙ β atTop (Icc 0 2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 2 ∧ (C : ℝ) * δ ≤ r ∧ β δ ≠ 0 ∧
      Tendsto (fun n => βₙ n δ) atTop (𝓝 (β δ)) := by
  let δ : ℝ := min 1 (r / ((C : ℝ) + 1))
  have hden : 0 < (C : ℝ) + 1 := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hr hden)
  have hδ2 : δ ≤ 2 := (min_le_left _ _).trans (by norm_num)
  have hprod : δ * ((C : ℝ) + 1) ≤ r := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hsmall : (C : ℝ) * δ ≤ r := by nlinarith
  have hne : β δ ≠ 0 := by
    intro he
    have hδ0 : δ = 0 := hβi ⟨hδ.le, hδ2⟩ ⟨le_rfl, by norm_num⟩ (he.trans hβ0.symm)
    exact hδ.ne' hδ0
  exact ⟨δ, hδ, hδ2, hsmall, hne, hconv.tendsto_at ⟨hδ.le, hδ2⟩⟩

/-- A convergent normalized guide family gives the full sequence passage
estimate, with hypotheses on deterministic continuation tubes and ribbon
coordinate regions. -/
theorem localized_sequence_success_of_uniform_guide_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F₀ : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (G ω) (F₀ ω))
    (hboundary : PublishedLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (Fₙ : ℕ → ℂ → ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hbar : ∀ n, ContinuousOn (Fbar n) closedHalfPlane)
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (Fₙ n z : OnePoint ℂ))
    (βₙ : ℕ → ℝ → ℂ)
    (hβc : ∀ n, ContinuousOn (βₙ n) (Icc 0 2)) (hβ0 : ∀ n, βₙ n 0 = 0)
    (hβHn : ∀ n t, t ∈ Icc (0 : ℝ) 2 → 0 ≤ (βₙ n t).im)
    (β : ℝ → ℂ) (hβlim0 : β 0 = 0) (hβlimi : InjOn β (Icc 0 2))
    (hβconv : TendstoUniformlyOn βₙ β atTop (Icc 0 2))
    (αₙ : ℕ → ℝ → ℂ) (aₙ : ℕ → ℂ) (Cg : ℝ≥0)
    (hα : ∀ n, LipschitzOnWith Cg (αₙ n) (Icc 0 2)) (hα0 : ∀ n, αₙ n 0 = aₙ n)
    (hmap : ∀ n t, t ∈ Icc (0 : ℝ) 2 → Fbar n (βₙ n t) = (αₙ n t : OnePoint ℂ))
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ q₀ b₀ b A d L₀ : ℝ,
      0 < q₀ ∧ 0 < b₀ ∧ 0 < b ∧ 0 < A ∧ 0 < d ∧ 1 < L₀ ∧
      ∀ (L : ℝ), L₀ ≤ L → A * L ^ (-d) ≤ q₀ / 2 →
      ∀ (B r : ℝ), 0 < B → 0 < r → B / 2 ≤ b₀ * L ^ b →
      ∀ (F : ℂ → ℂ), DifferentiableOn ℂ F upperHalfPlane →
      ∀ (a : ℂ) (O W : Set ℂ), IsOpen O → IsOpen W →
      ∀ (β : ℝ → ℂ) (tB T : ℝ), 0 < tB → tB < T →
      ContinuousOn β (Icc 0 T) → InjOn β (Icc 0 T) →
      (∀ t ∈ Ioc 0 T, 0 < (β t).im) → ‖β tB‖ = B →
      (∀ t ∈ Ioc tB T, B < ‖β t‖) →
      (∀ θ ∈ Ioo 0 Real.pi, ‖F (GuideSplice.circlePoint B θ) - a‖ < r / 4) →
      (∀ w : ℂ, B / 8 ≤ ‖w‖ → ‖w‖ ≤ B → ‖w‖ / 2 ≤ w.im → ‖F w - a‖ < r / 4) →
      F '' (β '' Icc tB T) ⊆ O → β T ∈ W →
      (∀ w ∈ upperHalfPlane, deriv F w ≠ 0) →
      TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane →
      ∀ (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ), IsOpen U →
      ContinuousOn p U → (∀ n, ContinuousOn (pₙ n) U) →
      TendstoLocallyUniformlyOn pₙ p atTop U →
      ball a (r / 2) ∪ O ⊆ U → (∀ w ∈ W, 1 < p (F w)) →
      (∀ w ∈ ball a (r / 4), p w < 1 / 3) →
      (∀ᶠ n in atTop, ball (aₙ n) (L * r₀) ⊆ U ∩ {w | pₙ n w < 1}) →
      ∀ (V : Set ℂ), IsOpen V → ball a (r / 2) ∪ O ⊆ V →
      ∀ (Vₙ : ℕ → Set ℂ), (∀ᶠ n in atTop, V ⊆ Vₙ n) →
      ∀ (bₙ : ℕ → ℂ) (ε : ℝ),
      (∀ n w, w ∈ Vₙ n → pₙ n w = 1 → ‖w - bₙ n‖ < ε / 4) →
      (∀ᶠ n in atTop, ball (aₙ n) (L * r₀) ⊆ Vₙ n) →
      ∀ (R : Set ℂ), IsOpen R →
      (∀ w ∈ ball a (r / 2) ∪ O, 1 / 3 < p w → p w < 2 / 3 → w ∈ R) →
      ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) → Tendsto v atTop (𝓝 0) →
      ∀ (η : ℕ → Ω → ℝ≥0 → ℂ), (∀ n, ∀ᵐ ω ∂P, Continuous (η n ω)) →
      (∀ n, ∀ᵐ ω ∂P, ∀ t, Fbar n (γ ω t) = (η n ω t : OnePoint ℂ)) →
      ∀ (Rₙ : ℕ → Set ℂ), (∀ᶠ n in atTop, R ⊆ Rₙ n) →
      ∃ c q : ℝ, 0 < c ∧ 0 < q ∧ ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P {ω |
        ω ∈ FrontSuccess η pₙ
          (fun ω => boundedFirstHeightTime (γ ω) B (T₀ * (Real.toNNReal B) ^ 2)) Vₙ bₙ ε n ∧
        ENNReal.ofReal c ≤ segmentSausageCharge κ (η n ω)
          (boundedFirstHeightTime (γ ω) B (T₀ * (Real.toNNReal B) ^ 2))
          (frontTime (fun t => pₙ n (η n ω t)) 1) (v n) (Rₙ n)} := by
  obtain ⟨δ, hδ, hδ2, hsmall, hz, hpoint⟩ :=
    small_initial_access_segment Cg r₀ hr₀ βₙ β hβlim0 hβlimi hβconv
  have hsub : Icc (0 : ℝ) δ ⊆ Icc 0 2 := Icc_subset_Icc_right hδ2
  exact localized_sequence_passage_success κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw
    hboundary hsupport Fₙ Fbar hFn hinj hbar hext δ hδ βₙ
    (fun n => (hβc n).mono hsub) hβ0 (fun n t ht => hβHn n t (hsub ht))
    (β δ) hz hpoint αₙ aₙ Cg (fun n => (hα n).mono hsub) hα0
    (fun n t ht => hmap n t (hsub ht)) r₀ hr₀ hsmall

end SLEExactGauge.SequencePassage

end

end OAI
