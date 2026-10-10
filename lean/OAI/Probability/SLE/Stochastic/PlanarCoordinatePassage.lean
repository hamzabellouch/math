import OAI.Probability.SLE.Gauge.ActualSequencePassageRegions
import OAI.Probability.SLE.Gauge.RibbonLimitSplice
import OAI.Probability.SLE.Stochastic.PlanarPassageNeighborhood

namespace OAI

/-! Passage along an actual convergent family of normalized charts and
ribbon coordinate maps. Every continuation tube, early-containment event,
and moving mass region is derived from the limiting coordinate guide. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.SequencePassage
open FirstHeightSupport EarlyPassageLocalization FirstFrontPassage PassageSuccess RibbonCoordinates

/-- A convergent recentered admissible family has a positive one-step passage-and-mass
probability at every sufficiently small mesh in a prescribed vanishing
sequence. The mass lies in the actual moving coordinate middle strip. -/
theorem planar_coordinate_limit_passage
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (G F₀ : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (G ω) (F₀ ω))
    (hboundary : PublishedLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (Qₙ : ℕ → ℂ → ℂ) (Q : ℂ → ℂ) (K : Set ℂ) (C Lq : ℝ≥0)
    (hC : 0 < C) (hLq : 0 < Lq)
    (hQu : ∀ n, LipschitzOnWith C (Qₙ n) K)
    (hQl : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ Lq * dist (Qₙ n x) (Qₙ n y))
    (hQconv : TendstoUniformlyOn Qₙ Q atTop K)
    (hQ : ContinuousOn Q K)
    (hbase : (1 : ℂ) ∈ K)
    (Fₙ : ℕ → ℂ → ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hbar : ∀ n, ContinuousOn (Fbar n) closedHalfPlane)
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (Fₙ n z : OnePoint ℂ))
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hiF : InjOn F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hFconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (αₙ βₙ : ℕ → ℝ → ℂ) (α β : ℝ → ℂ) (Cg : ℝ≥0)
    (hαL : ∀ n, LipschitzOnWith Cg (αₙ n) (Icc 0 2))
    (hαconv : TendstoUniformlyOn αₙ α atTop (Icc 0 2))
    (hα : ContinuousOn α (Icc 0 2))
    (hβc : ∀ n, ContinuousOn (βₙ n) (Icc 0 2)) (hβ0 : ∀ n, βₙ n 0 = 0)
    (hβHn : ∀ n t, t ∈ Icc (0 : ℝ) 2 → 0 ≤ (βₙ n t).im)
    (hmap : ∀ n t, t ∈ Icc (0 : ℝ) 2 → Fbar n (βₙ n t) = (αₙ n t : OnePoint ℂ))
    (hβconv : TendstoUniformlyOn βₙ β atTop (Icc 0 2))
    (hβ : ContinuousOn β (Icc 0 2)) (hβlim0 : β 0 = 0) (hβi : InjOn β (Icc 0 2))
    (hβH : MapsTo β (Ioc 0 2) upperHalfPlane)
    (hrel : EqOn (F ∘ β) α (Ioc 0 2)) (homit : α 0 ∉ F '' upperHalfPlane)
    (x ε ηtol : ℝ) (hx : |x| < ε) (hηtol : 0 < ηtol)
    (hshape : EqOn α (fun t => Q (guideCoordinate 0 x t)) (Icc 0 2))
    (hmem : ∀ t ∈ Icc (0 : ℝ) (3 / 2), guideCoordinate 0 x t ∈ interior K)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (hηc : ∀ n, ∀ᵐ ω ∂P, Continuous (η n ω))
    (hηbar : ∀ n, ∀ᵐ ω ∂P, ∀ t, Fbar n (γ ω t) = (η n ω t : OnePoint ℂ)) :
    ∃ B : ℝ, 0 < B ∧ ∃ Tc : ℝ≥0, 0 < Tc ∧ ∃ c q : ℝ, 0 < c ∧ 0 < q ∧
      ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P {ω |
        ω ∈ FrontSuccess η (fun n => longitudinalCoordinate (Qₙ n) K 0)
          (fun ω => boundedFirstHeightTime (γ ω) B Tc)
          (fun n => physicalPassageRegion (Qₙ n) K C ε ηtol) (fun n => Qₙ n 1) ηtol n ∧
        ENNReal.ofReal c ≤ segmentSausageCharge κ (η n ω)
          (boundedFirstHeightTime (γ ω) B Tc)
          (frontTime (fun t => longitudinalCoordinate (Qₙ n) K 0 (η n ω t)) 1)
          (v n) (physicalMiddleRegion (Qₙ n) K 0 ε)} := by
  let : IsProbabilityMeasure P := hB₀.isGaussianProcess.isProbabilityMeasure
  let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
  have ha := brownian_capacity_trace_adapted B₀ hm hc κ γ G F₀ hw
  have hγm (t : ℝ≥0) : Measurable (fun ω => γ ω t) := (ha t).mono (ℱ.le t) le_rfl
  have hSLE : IsOrdinaryChordalSLE κ γ P :=
    ⟨hγm, B₀, hB₀, Eventually.of_forall (fun ω => ⟨G ω, F₀ ω, hw ω⟩)⟩
  let pₙ := fun n => longitudinalCoordinate (Qₙ n) K 0
  let p := longitudinalCoordinate Q K 0
  let Vₙ := fun n => physicalPassageRegion (Qₙ n) K C ε ηtol
  let Rₙ := fun n => physicalMiddleRegion (Qₙ n) K 0 ε
  let aₙ := fun n => αₙ n 0
  obtain ⟨U, hU, hαU, _, _, hp, hpn, hpconv, hVlate, hterminal, hregion⟩ :=
    limiting_guide_passage_neighborhood_plane hplanar Qₙ Q K C Lq hC hLq hQu hQl hQconv
      hQ α hα x ε ηtol hx hηtol hshape hmem hbase
  have hprogress : ∀ t ∈ Icc (0 : ℝ) (3 / 2), p (α t) = t := by
    intro t ht
    have hiQ := lower_lipschitz_injOn Q K Lq
      (lower_lipschitz_uniform_limit Qₙ Q K Lq hQconv hQl)
    dsimp only [p]
    rw [hshape ⟨ht.1, ht.2.trans (by norm_num)⟩]
    simp only [longitudinalCoordinate, coordinateInverse_left hiQ (interior_subset (hmem t ht)),
      guideCoordinate_re, zero_add, sub_zero]
  have haU : α 0 ∈ U := hαU (mem_image_of_mem α ⟨le_rfl, by norm_num⟩)
  obtain ⟨r, hr, hball, hstartBall, hearly⟩ := eventual_early_coordinate_ball pₙ p U hU hp hpconv
    aₙ (α 0) haU (hprogress _ ⟨le_rfl, by norm_num⟩)
    (hαconv.tendsto_at ⟨le_rfl, by norm_num⟩)
  obtain ⟨T₀, hT₀, q₀, hq₀, hheight⟩ := uniform_bounded_firstHeight_real_probability
    κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw hsupport
  obtain ⟨b, A, d, L₀, hb, hA, hd, hL₀, hloc⟩ :=
    common_access_gives_firstHeight_localization κ hκ hκ8
  have ht : Tendsto (fun L : ℝ => A * L ^ (-d)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hd).const_mul A
  obtain ⟨L, hL, hsmall⟩ := ((eventually_ge_atTop L₀).and
    (ht.eventually (gt_mem_nhds (half_pos hq₀)))).exists
  have hLp : 0 < L := (zero_lt_one.trans hL₀).trans_le hL
  let r₀ := r / L
  have hr₀ : 0 < r₀ := div_pos hr hLp
  obtain ⟨δ, hδ, hδ2, hδsmall, hz, hpoint⟩ :=
    small_initial_access_segment Cg r₀ hr₀ βₙ β hβlim0 hβi hβconv
  have hδsub : Icc (0 : ℝ) δ ⊆ Icc 0 2 := Icc_subset_Icc_right hδ2
  obtain ⟨b₀, hb₀, hlocseq⟩ := hloc Ω P γ hSLE (fun ω => (hw ω).1)
    (fun ω => (hw ω).2.1) (fun ω t => (hw ω).2.2.1 t)
    Fₙ Fbar hFn hinj hbar hext δ hδ βₙ (fun n => (hβc n).mono hδsub) hβ0
    (fun n t ht => hβHn n t (hδsub ht)) (β δ) hz hpoint αₙ aₙ Cg
    (fun n => (hαL n).mono hδsub) (fun _ => rfl)
    (fun n t ht => hmap n t (hδsub ht)) r₀ hr₀ hδsmall
  have hβsub : Icc (0 : ℝ) (3 / 2) ⊆ Icc 0 2 := Icc_subset_Icc_right (by norm_num)
  obtain ⟨B, tB, hB, hBm, htB, htBT, hcross, hafter, hcircle, hsector, htail, hW,
      hend, hWfront⟩ := limiting_guide_splice_geometry F hF hiF α β (hα.mono hβsub)
    (hβ.mono hβsub) hβlim0 (fun t ht => hβH ⟨ht.1, ht.2.trans (by norm_num)⟩)
    (hrel.mono (Ioc_subset_Ioc le_rfl (by norm_num))) homit U hU p hp hαU hprogress
    r (b₀ * L ^ b) hr (mul_pos hb₀ (Real.rpow_pos_of_pos hLp _))
  let Tc := T₀ * (Real.toNNReal B) ^ 2
  have hTc : 0 < Tc := mul_pos hT₀ (pow_pos (Real.toNNReal_pos.mpr hB) 2)
  have hheightB := hheight B hB
  have hpositive : 0 < P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc) :=
    (ENNReal.ofReal_pos.mpr hq₀).trans_le hheightB
  have hLr : L * r₀ = r := by
    dsimp [r₀]
    exact mul_div_cancel₀ r hLp.ne'
  have hmissing : ∀ᶠ n in atTop, P (stoppedNarrowCertificate γ
      (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc \
        stoppedImageEvent γ (fun ω => boundedFirstHeightTime (γ ω) B Tc)
          (Fbar n) (aₙ n) r) ≤
      P (stoppedNarrowCertificate γ (fun ω => boundedFirstHeightTime (γ ω) B Tc) B Tc) / 2 := by
    filter_upwards [hlocseq] with n hn
    have hbound := hn L hL B hB hBm Tc
    rw [hLr] at hbound
    calc
      _ ≤ ENNReal.ofReal (A * L ^ (-d)) := hbound
      _ ≤ ENNReal.ofReal (q₀ / 2) := ENNReal.ofReal_le_ofReal hsmall.le
      _ = ENNReal.ofReal q₀ / 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      _ ≤ _ := ENNReal.div_le_div_right hheightB 2
  have hearlyAllowed : ∀ᶠ n in atTop, ball (aₙ n) r ⊆ Vₙ n := by
    filter_upwards [hearly, hVlate] with n hn hV
    exact (hn.trans inter_subset_left).trans hV
  obtain ⟨c, q, hcpos, hqpos, hprob⟩ := bounded_splice_sequence_success_middle_regions
    κ hκ hκ8 B₀ hB₀ hm hc γ G F₀ hw hboundary hsupport B r hB hr Tc F hF (α 0)
    U (limitingFrontTarget F p U) hU hW β tB (3 / 2) htB htBT
    (hβ.mono hβsub) (hβi.mono hβsub)
    (fun t ht => hβH ⟨ht.1, ht.2.trans (by norm_num)⟩)
    hcross hafter hcircle hsector htail hend Fbar hbar aₙ r Fₙ hFn hinj hne hFconv hext
    pₙ p U hU hp hpn hpconv (union_subset hball Subset.rfl) hWfront hstartBall hearly
    U hU (union_subset hball Subset.rfl) Vₙ hVlate (fun n => Qₙ n 1) ηtol hterminal
    hearlyAllowed v hv hlim η hηc hηbar Rₙ hregion hpositive hmissing
  exact ⟨B, hB, Tc, hTc, c, q, hcpos, hqpos, hprob⟩

end SLEExactGauge.SequencePassage

end

end OAI
