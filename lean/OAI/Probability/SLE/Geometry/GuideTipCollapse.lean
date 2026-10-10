import OAI.Probability.SLE.Geometry.InteriorVisit
import OAI.Probability.SLE.Geometry.GuideInteriorSeparation

namespace OAI

/-! Uniform collapse at the initial tip of access guides. The local uniform
limit is assumed here; the boundary collapse itself is proved using the
existing SLE localization estimate and a positive sausage seed. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- Finitely many initial continuous guides can be absorbed into a common
modulus once the tail has one. -/
theorem uniform_tip_modulus_of_eventually_uniform
    (β : ℕ → ℝ → ℂ) (T : ℝ) (hT : 0 < T)
    (hβ : ∀ n, ContinuousOn (β n) (Icc 0 T)) (hβ0 : ∀ n, β n 0 = 0)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ T ∧
      ∀ᶠ n in atTop, ∀ t ∈ Icc 0 h, ‖β n t‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ T ∧
      ∀ n t, t ∈ Icc 0 h → ‖β n t‖ < ε := by
  intro ε hε
  obtain ⟨h, hh, hhT, htail⟩ := htail ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  have hfinite : ∀ᶠ t in 𝓝[Icc 0 T] 0, ∀ n ∈ Finset.range N, ‖β n t‖ < ε := by
    apply (Finset.eventually_all _).mpr
    intro n _
    have hc := ((hβ n) 0 (mem_Icc.mpr ⟨le_rfl, hT.le⟩)).norm
    have hv : ‖β n 0‖ < ε := by simpa only [hβ0 n, norm_zero] using hε
    exact hc.eventually (Iio_mem_nhds hv)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.mem_nhdsWithin_iff.mp hfinite
  let h' := min h (δ / 2)
  have hh' : 0 < h' := lt_min hh (by positivity)
  have hh'h : h' ≤ h := min_le_left _ _
  refine ⟨h', hh', hh'h.trans hhT, ?_⟩
  intro n t ht
  by_cases hn : N ≤ n
  · exact hN n hn t ⟨ht.1, ht.2.trans hh'h⟩
  · apply hδbound
    · refine ⟨?_, ht.1, ht.2.trans (hh'h.trans hhT)⟩
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
      exact (ht.2.trans (min_le_right _ _)).trans_lt (by linarith)
    · exact Finset.mem_range.mpr (lt_of_not_ge hn)

lemma seed_ball_subset_halfPlane {z : ℂ} (hz : 2 < z.im) :
    closedBall z 2 ⊆ upperHalfPlane := by
  intro w hw
  have hh := Complex.im_le_norm (z - w)
  have hd := mem_closedBall.mp hw
  rw [Complex.sub_im, ← dist_eq_norm, dist_comm] at hh
  change 0 < w.im
  linarith

/-- Of two disjoint interior seed balls, at least one omits a given value
under an injective map. Compactness then gives a positive separation. -/
theorem exists_separated_seed_ball
    (F : ℂ → ℂ) (a : ℂ) (hF : ContinuousOn F upperHalfPlane)
    (hinj : InjOn F upperHalfPlane) :
    ∃ z : ℂ, 2 < z.im ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ w ∈ closedBall z 2, r₀ ≤ ‖F w - a‖ := by
  let z₁ : ℂ := 3 * Complex.I
  let z₂ : ℂ := 8 * Complex.I
  have hz₁ : 2 < z₁.im := by norm_num [z₁]
  have hz₂ : 2 < z₂.im := by norm_num [z₂]
  have hdisjoint : Disjoint (closedBall z₁ 2) (closedBall z₂ 2) := by
    apply Set.disjoint_left.mpr
    intro w hw₁ hw₂
    have hd := dist_triangle z₁ w z₂
    have h₁ : dist z₁ w ≤ 2 := by simpa only [dist_comm] using mem_closedBall.mp hw₁
    have h₂ := mem_closedBall.mp hw₂
    have he : dist z₁ z₂ = 5 := by
      rw [dist_eq_norm]
      norm_num [z₁, z₂, ← sub_mul, Complex.norm_mul]
    linarith
  have hex : ∃ z : ℂ, 2 < z.im ∧ ∀ w ∈ closedBall z 2, F w ≠ a := by
    by_cases h₁ : ∀ w ∈ closedBall z₁ 2, F w ≠ a
    · exact ⟨z₁, hz₁, h₁⟩
    · push Not at h₁
      obtain ⟨w₁, hw₁, hFw₁⟩ := h₁
      refine ⟨z₂, hz₂, ?_⟩
      intro w₂ hw₂ hFw₂
      have he := hinj (seed_ball_subset_halfPlane hz₁ hw₁)
        (seed_ball_subset_halfPlane hz₂ hw₂) (hFw₁.trans hFw₂.symm)
      exact Set.disjoint_left.mp hdisjoint hw₁ (he ▸ hw₂)
  obtain ⟨z, hz, hne⟩ := hex
  have hc : ContinuousOn (fun w => ‖F w - a‖) (closedBall z 2) :=
    ((hF.mono (seed_ball_subset_halfPlane hz)).sub continuousOn_const).norm
  obtain ⟨w, hw, hmin⟩ := (isCompact_closedBall z 2).exists_isMinOn
    (nonempty_closedBall.mpr (by norm_num)) hc
  exact ⟨z, hz, ‖F w - a‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hne w hw)), hmin⟩

theorem seed_ball_eventually_separated
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (aₙ : ℕ → ℂ) (a : ℂ)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (ha : Tendsto aₙ atTop (𝓝 a)) (hF : ContinuousOn F upperHalfPlane)
    (hinj : InjOn F upperHalfPlane) :
    ∃ z : ℂ, 2 < z.im ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ᶠ n in atTop, ∀ w ∈ closedBall z 2, r₀ ≤ ‖Fₙ n w - aₙ n‖ := by
  obtain ⟨z, hz, r₀, hr₀, hsep⟩ := exists_separated_seed_ball F a hF hinj
  have hu : TendstoUniformlyOn Fₙ F atTop (closedBall z 2) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall z 2)).mp (hconv.mono (seed_ball_subset_halfPlane hz))
  have herror : ∀ᶠ n in atTop, ∀ w ∈ closedBall z 2,
      dist (F w) (Fₙ n w) < r₀ / 4 :=
    hu _ (Metric.dist_mem_uniformity (by positivity : 0 < r₀ / 4))
  have haerror : ∀ᶠ n in atTop, dist (aₙ n) a < r₀ / 4 :=
    Metric.tendsto_nhds.mp ha (r₀ / 4) (by positivity)
  refine ⟨z, hz, r₀ / 2, by positivity, ?_⟩
  filter_upwards [herror, haerror] with n hn han
  intro w hw
  have hh : dist (F w) a ≤ dist (F w) (Fₙ n w) +
      dist (Fₙ n w) (aₙ n) + dist (aₙ n) a := by
    calc
      _ ≤ dist (F w) (Fₙ n w) + dist (Fₙ n w) a := dist_triangle _ _ _
      _ ≤ dist (F w) (Fₙ n w) + (dist (Fₙ n w) (aₙ n) + dist (aₙ n) a) :=
        by linarith [dist_triangle (Fₙ n w) (aₙ n) a]
      _ = _ := by ring
  have hs := hsep w hw
  have he := hn w hw
  rw [← dist_eq_norm] at hs ⊢
  linarith

/-- A locally convergent conformal family has a common tip
modulus. The physical guides have only a Lipschitz bound at their initial
point; no boundary modulus of continuity for the maps is assumed. -/
theorem uniform_tip_collapse
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (Fₙ : ℕ → ℂ → ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinjn : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hbar : ∀ n, ContinuousOn (Fbar n) {z : ℂ | 0 ≤ z.im})
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (Fₙ n z : OnePoint ℂ))
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (hF : ContinuousOn F upperHalfPlane) (hinj : InjOn F upperHalfPlane)
    (aₙ : ℕ → ℂ) (a : ℂ) (ha : Tendsto aₙ atTop (𝓝 a))
    (β : ℕ → ℝ → ℂ) (T C : ℝ) (hT : 0 < T) (hC : 0 < C)
    (hβ : ∀ n, ContinuousOn (β n) (Icc 0 T)) (hβ0 : ∀ n, β n 0 = 0)
    (hβH : ∀ n t, t ∈ Icc 0 T → 0 ≤ (β n t).im)
    (himage : ∀ n t, t ∈ Icc 0 T → ∃ w : ℂ,
      Fbar n (β n t) = (w : OnePoint ℂ) ∧ ‖w - aₙ n‖ ≤ C * t) :
    ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ T ∧
      ∀ n t, t ∈ Icc 0 h → ‖β n t‖ < ε := by
  apply uniform_tip_modulus_of_eventually_uniform β T hT hβ hβ0
  intro ε hε
  let scale : ℂ → ℂ := fun z => (ε : ℂ) * z
  have hscaleH : MapsTo scale upperHalfPlane upperHalfPlane := by
    intro z hz
    change 0 < ((ε : ℂ) * z).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos hε hz
  have hscaleC : Continuous scale := continuous_const.mul continuous_id
  have hscaleinj : Function.Injective scale := mul_right_injective₀ (by exact_mod_cast hε.ne')
  have hscaledconv := hconv.comp scale hscaleH hscaleC.continuousOn
  have hscaledF := hF.comp hscaleC.continuousOn hscaleH
  have hscaledinj : InjOn (F ∘ scale) upperHalfPlane :=
    fun x hx y hy hxy => hscaleinj (hinj (hscaleH hx) (hscaleH hy) hxy)
  obtain ⟨z, hz, r₀, hr₀, hsep⟩ := seed_ball_eventually_separated
    (fun n => Fₙ n ∘ scale) (F ∘ scale) aₙ a hscaledconv ha hscaledF hscaledinj
  let pres := Classical.choice (exists_regular_sle_presentation hSLE)
  let Q := P.comap (Subtype.val : pres.samples → Ω)
  have hsampleSLE : IsOrdinaryChordalSLE κ (fun ω : pres.samples => γ ω) Q :=
    ⟨fun t => (hSLE.1 t).comp measurable_subtype_coe, pres.B, pres.brownian,
      ae_of_all _ (fun ω => ⟨pres.G ω, pres.F ω, pres.witness ω⟩)⟩
  obtain ⟨Tvisit, R, _, _, hvisit⟩ := pres.positive_bounded_interior_visit hκ hκ8 z hz
  obtain ⟨rmin, hrmin, hbound⟩ := uniform_access_radius_lower_bound_of_interior_visit
    Q κ hκ hκ8 (fun ω : pres.samples => γ ω) hsampleSLE Tvisit R
    (closedBall z 2) (seed_ball_subset_halfPlane hz) hvisit r₀ hr₀
  let h : ℝ := min T (rmin / (2 * C))
  have hh : 0 < h := lt_min hT (div_pos hrmin (by positivity))
  have hhT : h ≤ T := min_le_left _ _
  have hCh : C * h < rmin := by
    have hb : h ≤ rmin / (2 * C) := min_le_right _ _
    have hb' := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp hb
    nlinarith
  refine ⟨h, hh, hhT, ?_⟩
  filter_upwards [hsep] with n hn
  intro t ht
  by_contra! hlarge
  have htT : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right (ht.2.trans hhT)
  have hnorm : ContinuousOn (fun s => ‖β n s‖) (Icc 0 t) :=
    (hβ n).norm.mono htT
  have hεmem : ε ∈ Icc ‖β n 0‖ ‖β n t‖ := by
    rw [hβ0 n, norm_zero]
    exact ⟨hε.le, hlarge⟩
  obtain ⟨S, hS, hnormS⟩ := intermediate_value_Icc ht.1 hnorm hεmem
  have hSpos : 0 < S := by
    by_contra hs
    have he : S = 0 := le_antisymm (le_of_not_gt hs) hS.1
    have hzero : (0 : ℝ) = ε := by simpa only [he, hβ0 n, norm_zero] using hnormS
    exact hε.ne' hzero.symm
  let η : ℝ → ℂ := fun s => (ε : ℂ)⁻¹ * β n s
  have hη : ContinuousOn η (Icc 0 S) :=
    continuousOn_const.mul ((hβ n).mono (Icc_subset_Icc_right (hS.2.trans (ht.2.trans hhT))))
  have hη0 : η 0 = 0 := by simp [η, hβ0 n]
  have hηS : ‖η S‖ = 1 := by
    simp only [η, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε, hnormS, inv_mul_cancel₀ hε.ne']
  have hηH : ∀ s ∈ Icc 0 S, 0 ≤ (η s).im := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans (hS.2.trans (ht.2.trans hhT))⟩
    simpa only [η, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] using mul_nonneg (inv_nonneg.mpr hε.le) (hβH n s hsT)
  have hscaledbar : ContinuousOn (Fbar n ∘ scale) {z : ℂ | 0 ≤ z.im} := by
    apply (hbar n).comp hscaleC.continuousOn
    intro z hz
    change 0 ≤ ((ε : ℂ) * z).im
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_nonneg hε.le hz
  have hηimage : ∀ s ∈ Icc 0 S, ∃ w : ℂ,
      (Fbar n ∘ scale) (η s) = (w : OnePoint ℂ) ∧ ‖w - aₙ n‖ ≤ C * h := by
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans (hS.2.trans (ht.2.trans hhT))⟩
    obtain ⟨w, hw, hwd⟩ := himage n s hsT
    refine ⟨w, ?_, hwd.trans (mul_le_mul_of_nonneg_left (hs.2.trans (hS.2.trans ht.2)) hC.le)⟩
    simpa only [Function.comp_apply, scale, η, ← mul_assoc,
      mul_inv_cancel₀ (show (ε : ℂ) ≠ 0 by exact_mod_cast hε.ne'), one_mul] using hw
  have hscaledFn : DifferentiableOn ℂ (Fₙ n ∘ scale) upperHalfPlane :=
    (hFn n).comp (((differentiable_const (ε : ℂ)).mul differentiable_id).differentiableOn) hscaleH
  have hscaledInjn : InjOn (Fₙ n ∘ scale) upperHalfPlane :=
    fun x hx y hy hxy => hscaleinj (hinjn n (hscaleH hx) (hscaleH hy) hxy)
  have hscaledExt : ∀ w ∈ upperHalfPlane,
      (Fbar n ∘ scale) w = ((Fₙ n ∘ scale) w : OnePoint ℂ) :=
    fun w hw => hext n _ (hscaleH hw)
  exact (not_lt_of_ge (hbound (Fₙ n ∘ scale) (Fbar n ∘ scale) hscaledFn
    hscaledInjn hscaledbar hscaledExt (aₙ n) (C * h) (mul_pos hC hh) hn
    η S hSpos hη hη0 hηS hηH hηimage)) hCh

end SLEExactGauge

end

end OAI
