import OAI.Probability.SLE.SausageSeedAll
import OAI.Probability.SLE.Geometry.AccessGuideCollapse

namespace OAI

/-! A positive bounded interior visit, obtained from the already proved
sausage seed. This supplies the nondegeneracy event in the access-guide
argument without a uniform support assumption. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

theorem RegularSLEPresentation.positive_bounded_interior_visit
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (z : ℂ) (hz : 2 < z.im) :
    ∃ (T : ℝ≥0) (R : ℝ), 0 < T ∧ 0 < R ∧
      0 < (P.comap (Subtype.val : a.samples → Ω))
        {ω | (∀ t ∈ Icc 0 T, ‖γ ω t‖ < R) ∧
          ∃ t ∈ Icc 0 T, γ ω t ∈ closedBall z 2} := by
  obtain ⟨T, p, b, e₀, hT, hp, hb, he₀, hseed⟩ :=
    a.source_positive_probability_initial_sausage_all hκ hκ8 z hz
  let e : ℝ := min (e₀ / 2) (1 / 2)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have hee₀ : e < e₀ := (min_le_left _ _).trans_lt (by linarith)
  have hehalf : e ≤ 1 / 2 := min_le_right _ _
  let Q := P.comap (Subtype.val : a.samples → Ω)
  let A : Set a.samples := {ω | ENNReal.ofReal b ≤ ENNReal.ofReal
    (e ^ (-codimension κ)) * volume (closedBall z 1 ∩ sourceSausageSet (γ ω) 0 T e)}
  let E : ℕ → Set a.samples := fun n =>
    {ω | (∀ t ∈ Icc 0 T, ‖γ ω t‖ < (n : ℝ)) ∧
      ∃ t ∈ Icc 0 T, γ ω t ∈ closedBall z 2}
  have hApos : 0 < Q A := (ENNReal.ofReal_pos.mpr hp).trans_le (hseed e he hee₀)
  have hsub : A ⊆ ⋃ n : ℕ, E n := by
    intro ω hω
    have hnonempty : (closedBall z 1 ∩ sourceSausageSet (γ ω) 0 T e).Nonempty := by
      by_contra hn
      have hempty := Set.not_nonempty_iff_eq_empty.mp hn
      have hh := hω
      change ENNReal.ofReal b ≤ ENNReal.ofReal (e ^ (-codimension κ)) *
        volume (closedBall z 1 ∩ sourceSausageSet (γ ω) 0 T e) at hh
      rw [hempty, measure_empty, mul_zero] at hh
      exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hb)) hh
    obtain ⟨w, hwball, u, hu, hdist⟩ := hnonempty
    have huQ : γ ω u ∈ closedBall z 2 := by
      apply mem_closedBall.mpr
      have hh := dist_triangle (γ ω u) w z
      have hw := mem_closedBall.mp hwball
      have hd : dist (γ ω u) w < e := by simpa only [dist_comm] using hdist
      linarith
    have hbounded : Bornology.IsBounded (γ ω '' Icc 0 T) :=
      (isCompact_Icc.image (a.trace_continuous ω)).isBounded
    obtain ⟨M, hM, hbound⟩ := hbounded.exists_pos_norm_lt
    obtain ⟨n, hn⟩ := exists_nat_gt M
    apply mem_iUnion.mpr
    refine ⟨n, ?_, u, hu, huQ⟩
    intro t ht
    exact (hbound _ (mem_image_of_mem (γ ω) ht)).trans hn
  have hex : ∃ n : ℕ, 0 < Q (E n) := by
    by_contra! hnone
    have hnull : ∀ n, Q (E n) = 0 := fun n => le_antisymm (hnone n) bot_le
    have hu : Q (⋃ n : ℕ, E n) = 0 := measure_iUnion_null_iff.mpr hnull
    exact (not_le_of_gt hApos) ((measure_mono hsub).trans_eq hu)
  obtain ⟨n, hn⟩ := hex
  have hnpos : 0 < (n : ℝ) := by
    by_contra h
    have hE : E n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have hh := hω.1 0 (mem_Icc.mpr ⟨le_rfl, zero_le⟩)
      exact (not_lt_of_ge ((le_of_not_gt h).trans (norm_nonneg _))) hh
    rw [hE, measure_empty] at hn
    exact (lt_irrefl 0) hn
  exact ⟨T, n, hT, hnpos, hn⟩

/-- Localization only needs an interior visit before the bounded time,
not a visit at a predetermined terminal time. -/
theorem uniform_access_radius_lower_bound_of_interior_visit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (T : ℝ≥0) (R : ℝ) (Q : Set ℂ) (hQ : Q ⊆ upperHalfPlane)
    (hvisit : 0 < P {ω | (∀ t ∈ Icc 0 T, ‖γ ω t‖ < R) ∧
      ∃ t ∈ Icc 0 T, γ ω t ∈ Q})
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
  let E : Set Ω := {ω | (∀ t ∈ Icc 0 T, ‖γ ω t‖ < R) ∧
    ∃ t ∈ Icc 0 T, γ ω t ∈ Q}
  have ht : Tendsto (fun L : ℝ => ENNReal.ofReal (C * L ^ (-c))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_rpow_neg_atTop hc).const_mul C)
  obtain ⟨L, hL, hLR, hLprob⟩ := ((eventually_ge_atTop L₀).and
    (((tendsto_rpow_atTop hb).eventually_gt_atTop R).and
      (ht.eventually (gt_mem_nhds hvisit)))).exists
  have hLp : 0 < L := (zero_lt_one.trans hL₀).trans_le hL
  refine ⟨r₀ / L, div_pos hr₀ hLp, ?_⟩
  intro F Fbar hF hinj hbar hext a r hr hsep η S hS hη hη0 hηS hupper himage
  by_contra! hsmall
  have hLr : L * r < r₀ := by
    simpa only [mul_comm] using (lt_div_iff₀ hLp).mp hsmall
  have hbound := hloc Ω inferInstance P inferInstance γ hSLE F Fbar hF hinj
    hbar hext a r hr η S hS hη hη0 hηS hupper himage L hL
  have hsub : E ⊆ {ω | ∃ t : ℝ≥0, BeforeFirstModulus (γ ω) (L ^ b) t ∧
      Fbar (γ ω t) ∉ (fun z : ℂ => (z : OnePoint ℂ)) '' ball a (L * r)} := by
    rintro ω ⟨hω, t, ht, hωQ⟩
    refine ⟨t, ?_, ?_⟩
    · intro s hs
      exact (hω s ⟨zero_le, hs.le.trans ht.2⟩).trans hLR
    · rintro ⟨w, hw, he⟩
      have heq : w = F (γ ω t) :=
        OnePoint.coe_injective (he.trans (hext _ (hQ hωQ)))
      subst w
      have hh : ‖F (γ ω t) - a‖ < L * r := by
        simpa only [mem_ball, dist_eq_norm] using hw
      exact (not_lt_of_ge (hsep _ hωQ)) (hh.trans hLr)
  exact (not_lt_of_ge ((measure_mono hsub).trans hbound)) hLprob

end SLEExactGauge

end

end OAI
