import OAI.Probability.SLE.Gauge.SequencePassage
import OAI.Probability.SLE.Gauge.PassageSuccess

namespace OAI

/-! Successful sequence passage: full allowed-ribbon containment and the
terminal tip offset accompany the actual stopped sausage lower bound. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.SequencePassage
open FirstHeightSupport EarlyPassageLocalization FirstFrontPassage PassageSuccess

local instance successSequencePathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance successSequencePathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem bounded_splice_sequence_success
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
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F upperHalfPlane) (a : ℂ)
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
    (Fₙ : ℕ → ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (Fₙ n z : OnePoint ℂ))
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hpn : ∀ n, ContinuousOn (pₙ n) U)
    (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (hOU : ball a (r / 2) ∪ O ⊆ U)
    (hWfront : ∀ z ∈ W, 1 < p (F z))
    (hstartBall : ∀ z ∈ ball a (r / 4), p z < 1 / 3)
    (hearlyBall : ∀ᶠ n in atTop, ball (aₙ n) ρ ⊆ U ∩ {z | pₙ n z < 1})
    (V : Set ℂ) (hV : IsOpen V) (hOV : ball a (r / 2) ∪ O ⊆ V)
    (Vₙ : ℕ → Set ℂ) (hVVₙ : ∀ᶠ n in atTop, V ⊆ Vₙ n)
    (bₙ : ℕ → ℂ) (ε : ℝ)
    (hterminal : ∀ n z, z ∈ Vₙ n → pₙ n z = 1 → ‖z - bₙ n‖ < ε / 4)
    (hearlyAllowed : ∀ᶠ n in atTop, ball (aₙ n) ρ ⊆ Vₙ n)
    (R : Set ℂ) (hR : IsOpen R)
    (hmiddle : ∀ z ∈ ball a (r / 2) ∪ O, 1 / 3 < p z → p z < 2 / 3 → z ∈ R)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (hηc : ∀ n, ∀ᵐ ω ∂P, Continuous (η n ω))
    (hηbar : ∀ n, ∀ᵐ ω ∂P, ∀ t, Fbar n (γ ω t) = (η n ω t : OnePoint ℂ))
    (Rₙ : ℕ → Set ℂ) (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
    (hpositive : 0 < P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc))
    (hmissing : ∀ᶠ n in atTop, P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc \
        stoppedImageEvent γ (fun ω => boundedFirstHeightTime (γ ω) B Tc)
          (Fbar n) (aₙ n) ρ) ≤
      P (stoppedNarrowCertificate γ (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc) / 2) :
    ∃ c q : ℝ, 0 < c ∧ 0 < q ∧ ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P {ω |
      ω ∈ FrontSuccess η pₙ (fun ω => boundedFirstHeightTime (γ ω) B Tc) Vₙ bₙ ε n ∧
      ENNReal.ofReal c ≤ segmentSausageCharge κ (η n ω)
        (boundedFirstHeightTime (γ ω) B Tc)
        (frontTime (fun t => pₙ n (η n ω t)) 1) (v n) (Rₙ n)} := by
  let : IsProbabilityMeasure P := hB₀.isGaussianProcess.isProbabilityMeasure
  let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
  let σ := fun ω => boundedFirstHeightTime (γ ω) B Tc
  have ha := brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw
  have hγm (t : ℝ≥0) : Measurable (fun ω => γ ω t) := (ha t).mono (ℱ.le t) le_rfl
  have hSLE : IsOrdinaryChordalSLE κ γ P :=
    ⟨hγm, B₀, hB₀, Eventually.of_forall (fun ω => ⟨G ω, F₀ ω, hw ω⟩)⟩
  have hσ := boundedFirstHeightTime_isStoppingTime ℱ γ ha (fun ω => (hw ω).1) B Tc
  have hσm : Measurable σ := stopping_time_measurable_nnreal hσ
  let f := sourceTracePath γ (fun ω => (hw ω).1)
  have hfm : Measurable f := source_path_measurable f hγm
  let Uparam := parameterContinuationRegion F a r O
  have hUparam : IsOpen Uparam := parameterContinuationRegion_isOpen hF.continuousOn a r hO
  let C := stoppedPhysicalTube γ σ Uparam W
  let E := stoppedNarrowCertificate γ σ B Tc ∩ C
  let H : ℕ → Set Ω := fun n => stoppedImageEvent γ σ (Fbar n) (aₙ n) ρ
  have hEm : MeasurableSet E := by
    apply MeasurableSet.inter
    · exact hσ.measurableSpace_le _
        (boundedFirstHeight_certificate_measurable ℱ γ ha (fun ω => (hw ω).1) B Tc)
    · exact measurableSet_stoppedPhysicalTube γ (fun ω => (hw ω).1) hγm σ hσm Uparam W hUparam hW
  have hstart : ∀ ω ∈ E, p (F (γ ω (σ ω))) < 1 / 3 := by
    intro ω hω
    have hnorm := bounded_firstHeight_norm (f ω) (hw ω).2.1 (hw ω).2.2.1
      hB Tc hω.1 (σ ω) ⟨bot_le, le_rfl⟩
    change ‖γ ω (σ ω)‖ < B / 2 at hnorm
    have hheight : (γ ω (σ ω)).im = B / 4 := hω.1.2.1
    have him := Complex.im_le_norm (γ ω (σ ω))
    have hsmall := hsector (γ ω (σ ω)) (by linarith) (by linarith)
      (by rw [hheight]; linarith)
    exact hstartBall _ (by simpa only [mem_ball, dist_eq_norm] using hsmall)
  obtain ⟨q, hq, hprob⟩ := eventual_bounded_splice_probability κ hκ hκ8 B₀ hB₀ hm hc
    γ G F₀ hw hboundary hsupport B r hB hr Tc F hF.continuousOn a O W hO hW
    β tB T htB htBT hβ hi hβH hcross hafter hcircle hsector htail hend Fbar hbar aₙ ρ
    hpositive hmissing
  have hη : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω ≤ t → γ ω t ∈ upperHalfPlane →
      η n ω t = Fₙ n (γ ω t) := by
    intro n
    filter_upwards [hηbar n] with ω hω
    intro t _ ht
    exact OnePoint.coe_injective ((hω t).symm.trans (hext n _ ht))
  have hearly : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ H n ∩ E →
      MapsTo (η n ω) (Icc 0 (σ ω)) U ∧
        ∀ t ∈ Icc 0 (σ ω), pₙ n (η n ω t) < 1 := by
    filter_upwards [hearlyBall] with n hn
    filter_upwards [hηbar n] with ω hω
    intro hmem
    have himage : MapsTo (η n ω) (Icc 0 (σ ω)) (ball (aₙ n) ρ) := by
      intro t ht
      obtain ⟨z, hz, he⟩ := hmem.1 t ht
      have heq : z = η n ω t := OnePoint.coe_injective (he.trans (hω t))
      exact heq ▸ hz
    exact ⟨fun _ ht => (hn (himage ht)).1, fun _ ht => (hn (himage ht)).2⟩
  have hearlyV : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ H n ∩ E →
      MapsTo (η n ω) (Icc 0 (σ ω)) (Vₙ n) := by
    filter_upwards [hearlyAllowed] with n hn
    filter_upwards [hηbar n] with ω hω
    intro hmem t ht
    obtain ⟨z, hz, he⟩ := hmem.1 t ht
    have heq : z = η n ω t := OnePoint.coe_injective (he.trans (hω t))
    exact hn (heq ▸ hz)
  obtain ⟨c, hcpos, hmass⟩ := retained_tube_firstFront_success_mass P κ hκ hκ8
    f hfm hSLE σ hσm Fₙ F hFn hinj hF hne hconv Uparam W hUparam inter_subset_left
    pₙ p U hU hp hpn hpconv (fun _ hz => hOU hz.2) hWfront E hEm inter_subset_right
    hstart V hV (fun _ hz => hOV hz.2) Vₙ hVVₙ bₙ ε hterminal
    R hR (fun _ hz => hmiddle _ hz.2) v hv hlim η Rₙ hregion H q hq hprob hη hηc hearly hearlyV
  exact ⟨c, q / 8, hcpos, by positivity, hmass⟩


theorem localized_sequence_passage_success
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
    (δ : ℝ) (hδ : 0 < δ) (βₙ : ℕ → ℝ → ℂ)
    (hβc : ∀ n, ContinuousOn (βₙ n) (Icc 0 δ)) (hβ0 : ∀ n, βₙ n 0 = 0)
    (hβHn : ∀ n t, t ∈ Icc 0 δ → 0 ≤ (βₙ n t).im)
    (z : ℂ) (hz : z ≠ 0) (hβconv : Tendsto (fun n => βₙ n δ) atTop (𝓝 z))
    (αₙ : ℕ → ℝ → ℂ) (aₙ : ℕ → ℂ) (Cg : ℝ≥0)
    (hα : ∀ n, LipschitzOnWith Cg (αₙ n) (Icc 0 δ)) (hα0 : ∀ n, αₙ n 0 = aₙ n)
    (hmap : ∀ n t, t ∈ Icc 0 δ → Fbar n (βₙ n t) = (αₙ n t : OnePoint ℂ))
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hsmallGuide : (Cg : ℝ) * δ ≤ r₀) :
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
  let : IsProbabilityMeasure P := hB₀.isGaussianProcess.isProbabilityMeasure
  let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
  have ha := brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw
  have hγm (t : ℝ≥0) : Measurable (fun ω => γ ω t) := (ha t).mono (ℱ.le t) le_rfl
  have hSLE : IsOrdinaryChordalSLE κ γ P :=
    ⟨hγm, B₀, hB₀, Eventually.of_forall (fun ω => ⟨G ω, F₀ ω, hw ω⟩)⟩
  obtain ⟨T₀, hT₀, q₀, hq₀, hheight⟩ := uniform_bounded_firstHeight_real_probability
    κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw hsupport
  obtain ⟨b, A, d, L₀, hb, hA, hd, hL₀, hloc⟩ :=
    common_access_gives_firstHeight_localization κ hκ hκ8
  obtain ⟨b₀, hb₀, hlocseq⟩ := hloc Ω P γ hSLE (fun ω => (hw ω).1)
    (fun ω => (hw ω).2.1) (fun ω t => (hw ω).2.2.1 t)
    Fₙ Fbar hFn hinj hbar hext δ hδ βₙ hβc hβ0 hβHn z hz hβconv
    αₙ aₙ Cg hα hα0 hmap r₀ hr₀ hsmallGuide
  refine ⟨T₀, hT₀, q₀, b₀, b, A, d, L₀, hq₀, hb₀, hb, hA, hd, hL₀, ?_⟩
  intro L hL hsmall B r hB hr hBL F hF a O W hO hW β tB T htB htBT hβ hi hβH
    hcross hafter hcircle hsector htail hend hne hconv pₙ p U hU hp hpn hpconv hOU
    hWfront hstartBall hearlyBall V hV hOV Vₙ hVVₙ bₙ ε hterminal hearlyAllowed
    R hR hmiddle v hv hlim η hηc hηbar Rₙ hregion
  let Tc := T₀ * (Real.toNNReal B) ^ 2
  have hheightB := hheight B hB
  have hpositive : 0 < P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc) :=
    (ENNReal.ofReal_pos.mpr hq₀).trans_le hheightB
  have hmissing : ∀ᶠ n in atTop, P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc \
        stoppedImageEvent γ (fun ω => boundedFirstHeightTime (γ ω) B Tc)
          (Fbar n) (aₙ n) (L * r₀)) ≤
      P (stoppedNarrowCertificate γ (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc) / 2 := by
    filter_upwards [hlocseq] with n hn
    calc
      _ ≤ ENNReal.ofReal (A * L ^ (-d)) := hn L hL B hB hBL Tc
      _ ≤ ENNReal.ofReal (q₀ / 2) := ENNReal.ofReal_le_ofReal hsmall
      _ = ENNReal.ofReal q₀ / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ _ := ENNReal.div_le_div_right hheightB 2
  exact bounded_splice_sequence_success κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw hboundary hsupport
    B r hB hr Tc F hF a O W hO hW β tB T htB htBT hβ hi hβH hcross hafter hcircle hsector
    htail hend Fbar hbar aₙ (L * r₀) Fₙ hFn hinj hne hconv hext pₙ p U hU hp hpn hpconv
    hOU hWfront hstartBall hearlyBall V hV hOV Vₙ hVVₙ bₙ ε hterminal hearlyAllowed
    R hR hmiddle v hv hlim η hηc hηbar Rₙ hregion hpositive hmissing

end SLEExactGauge.SequencePassage

end

end OAI
