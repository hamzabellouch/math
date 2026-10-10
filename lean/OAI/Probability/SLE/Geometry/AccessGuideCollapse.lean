import OAI.Probability.SLE.Loewner.SlitSupport
import OAI.Probability.SLE.StripProbabilities

namespace OAI

/-! Uniform collapse of access guides from the already proved conformal
localization estimate and pointwise slit support. An interior separated set
prevents arbitrarily small physical images of a unit-modulus access guide. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem uniform_access_image_radius_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (T : ℝ≥0) (R : ℝ) (Q : Set ℂ) (hQ : Q ⊆ upperHalfPlane)
    (hvisit : 0 < P {ω | (∀ t ∈ Icc 0 T, ‖γ ω t‖ < R) ∧ γ ω T ∈ Q})
    (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ rmin : ℝ, 0 < rmin ∧
      ∀ (F : ℂ → ℂ) (Fbar : ℂ → OnePoint ℂ),
      DifferentiableOn ℂ F upperHalfPlane → InjOn F upperHalfPlane →
      ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} →
      (∀ z ∈ upperHalfPlane, Fbar z = (F z : OnePoint ℂ)) →
      ∀ (a : ℂ) (r : ℝ), 0 < r →
      (∀ z ∈ Q, r₀ ≤ ‖F z - a‖) →
      ∀ (η : ℝ → ℂ) (S : ℝ), 0 < S → ContinuousOn η (Icc 0 S) →
      η 0 = 0 → ‖η S‖ = 1 → (∀ t ∈ Icc 0 S, 0 ≤ (η t).im) →
      (∀ t ∈ Icc 0 S, ∃ w : ℂ,
        Fbar (η t) = (w : OnePoint ℂ) ∧ ‖w - a‖ ≤ r) → rmin ≤ r := by
  obtain ⟨b, C, c, L₀, hb, _, hc, hL₀, hloc⟩ :=
    sourceUniformConformalLocalization κ hκ hκ8
  let E : Set Ω := {ω | (∀ t ∈ Icc 0 T, ‖γ ω t‖ < R) ∧ γ ω T ∈ Q}
  have ht : Tendsto (fun L : ℝ => ENNReal.ofReal (C * L ^ (-c))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_rpow_neg_atTop hc).const_mul C)
  have hlarge := (eventually_ge_atTop L₀).and
    (((tendsto_rpow_atTop hb).eventually_gt_atTop R).and
      (ht.eventually (gt_mem_nhds hvisit)))
  obtain ⟨L, hL, hLR, hLprob⟩ := hlarge.exists
  have hLp : 0 < L := (zero_lt_one.trans hL₀).trans_le hL
  refine ⟨r₀ / L, div_pos hr₀ hLp, ?_⟩
  intro F Fbar hF hinj hbar hext a r hr hsep η S hS hη hη0 hηS hupper himage
  by_contra! hsmall
  have hLr : L * r < r₀ := by
    have hh := (lt_div_iff₀ hLp).mp hsmall
    simpa only [mul_comm] using hh
  have hbound := hloc Ω inferInstance P inferInstance γ hSLE F Fbar hF hinj
    hbar hext a r hr η S hS hη hη0 hηS hupper himage L hL
  have hsub : E ⊆ {ω | ∃ t : ℝ≥0, BeforeFirstModulus (γ ω) (L ^ b) t ∧
      Fbar (γ ω t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' ball a (L * r)} := by
    rintro ω ⟨hω, hωQ⟩
    refine ⟨T, ?_, ?_⟩
    · intro s hs
      exact (hω s ⟨zero_le, hs.le⟩).trans hLR
    · rintro ⟨w, hw, he⟩
      have heq : w = F (γ ω T) :=
        OnePoint.coe_injective (he.trans (hext _ (hQ hωQ)))
      subst w
      have hh : ‖F (γ ω T) - a‖ < L * r := by
        simpa only [mem_ball, dist_eq_norm] using hw
      exact (not_lt_of_ge (hsep _ hωQ)) (hh.trans hLr)
  exact (not_lt_of_ge ((measure_mono hsub).trans hbound)) hLprob

/-- The separated interior set and published pointwise support rule out the
bad sequence in the access-guide compactness argument. All map and guide
conditions refer to the actual complex maps, rather than to an abstract state. -/
theorem no_shrinking_access_guides_of_published_support
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hpublished : PublishedSimpleTraceSupport P γ)
    (T : ℝ≥0) (hT : 0 < T) (β : ℝ≥0 → ℂ) (U : ℝ≥0 → ℝ)
    (hU : Continuous U) (hβ : IsCapacityTwoTrace U β)
    (hinjβ : InjOn β (Icc 0 T)) (hβH : ∀ t ∈ Ioc 0 T, β t ∈ upperHalfPlane)
    (R : ℝ) (hβR : β '' Icc 0 T ⊆ ball 0 R)
    (Q : Set ℂ) (hQopen : IsOpen Q) (hQ : Q ⊆ upperHalfPlane) (hβQ : β T ∈ Q)
    (F : ℕ → ℂ → ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ)
    (hF : ∀ n, DifferentiableOn ℂ (F n) upperHalfPlane)
    (hinj : ∀ n, InjOn (F n) upperHalfPlane)
    (hbar : ∀ n, ContinuousOn (Fbar n) {z : ℂ | 0 ≤ z.im})
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (F n z : OnePoint ℂ))
    (a : ℕ → ℂ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hlim : Tendsto r atTop (𝓝 0)) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hsep : ∀ᶠ n in atTop, ∀ z ∈ Q, r₀ ≤ ‖F n z - a n‖)
    (η : ℕ → ℝ → ℂ) (S : ℕ → ℝ) (hS : ∀ n, 0 < S n)
    (hη : ∀ n, ContinuousOn (η n) (Icc 0 (S n)))
    (hη0 : ∀ n, η n 0 = 0) (hηS : ∀ n, ‖η n (S n)‖ = 1)
    (hupper : ∀ n t, t ∈ Icc 0 (S n) → 0 ≤ (η n t).im)
    (himage : ∀ n t, t ∈ Icc 0 (S n) → ∃ w : ℂ,
      Fbar n (η n t) = (w : OnePoint ℂ) ∧ ‖w - a n‖ ≤ r n) : False := by
  have hp := slit_tube_support_of_published_support P γ hpublished T hT β U hU hβ
    hinjβ hβH (ball 0 R) Q isOpen_ball hQopen hβR hβQ
  have hvisit : 0 < P {ω | (∀ t ∈ Icc 0 T, ‖γ ω t‖ < R) ∧ γ ω T ∈ Q} := by
    simpa only [mem_ball, dist_zero_right] using hp
  obtain ⟨rmin, hrmin, hbound⟩ := uniform_access_image_radius_lower_bound
    P κ hκ hκ8 γ hSLE T R Q hQ hvisit r₀ hr₀
  obtain ⟨n, hn, hsepn⟩ := ((hlim.eventually (gt_mem_nhds hrmin)).and hsep).exists
  exact (not_lt_of_ge (hbound (F n) (Fbar n) (hF n) (hinj n) (hbar n)
    (hext n) (a n) (r n) (hr n) hsepn (η n) (S n) (hS n) (hη n)
    (hη0 n) (hηS n) (hupper n) (himage n))) hn

end SLEExactGauge

end

end OAI
