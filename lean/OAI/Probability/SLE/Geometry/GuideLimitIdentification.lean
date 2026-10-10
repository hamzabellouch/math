import OAI.Probability.SLE.Geometry.HyperbolicGuideCompactness
import OAI.Probability.SLE.Geometry.GuideTipCollapse

namespace OAI

/-!
Identification of parameter-guide limits. Compact containment and injectivity
give a uniform inverse modulus for the limiting conformal map, so the whole
sequence converges once the physical guides do.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

namespace SLEExactGauge.GuideLimitIdentification

/-- An injective continuous map on a compact set has a uniform inverse
modulus, stated directly in the ambient complex plane. -/
theorem compact_inverse_modulus
    {F : ℂ → ℂ} {Q : Set ℂ} (hQ : IsCompact Q)
    (hF : ContinuousOn F Q) (hi : InjOn F Q) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ Q, ∀ y ∈ Q, dist (F x) (F y) < η → dist x y < ε := by
  intro ε hε
  let D := (Q ×ˢ Q) ∩ {p : ℂ × ℂ | ε ≤ dist p.1 p.2}
  have hD : IsCompact D := (hQ.prod hQ).inter_right
    (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
  have hc₁ : ContinuousOn (fun p : ℂ × ℂ => F p.1) D :=
    hF.comp continuous_fst.continuousOn (fun _ hp => hp.1.1)
  have hc₂ : ContinuousOn (fun p : ℂ × ℂ => F p.2) D :=
    hF.comp continuous_snd.continuousOn (fun _ hp => hp.1.2)
  have hc : ContinuousOn (fun p : ℂ × ℂ => dist (F p.1) (F p.2)) D :=
    continuous_dist.comp_continuousOn (hc₁.prodMk hc₂)
  by_cases hne : D.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hD.exists_isMinOn hne hc
    have hxy : p.1 ≠ p.2 := by
      intro he
      have hh : ε ≤ dist p.1 p.2 := hp.2
      rw [he, dist_self] at hh
      linarith
    have hpF : F p.1 ≠ F p.2 := fun he => hxy (hi hp.1.1 hp.1.2 he)
    refine ⟨dist (F p.1) (F p.2), dist_pos.mpr hpF, ?_⟩
    intro x hx y hy hdist
    by_contra hn
    have hxyD : (x, y) ∈ D := ⟨⟨hx, hy⟩, le_of_not_gt hn⟩
    exact (not_le_of_gt hdist) (hmin hxyD)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx y hy _
    by_contra hn
    exact hne ⟨(x, y), ⟨⟨hx, hy⟩, le_of_not_gt hn⟩⟩

/-- Uniform convergence of the physical curves and of the conformal maps on
the common compact set gives uniform convergence after applying the limiting
map to the parameter curves. -/
theorem limiting_map_composition_tendsto
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (βₙ αₙ : ℕ → ℝ → ℂ) (α : ℝ → ℂ)
    {Q : Set ℂ} {I : Set ℝ}
    (hF : TendstoUniformlyOn Fₙ F atTop Q)
    (hα : TendstoUniformlyOn αₙ α atTop I)
    (hQ : ∀ n, MapsTo (βₙ n) I Q)
    (hrelation : ∀ n t, t ∈ I → Fₙ n (βₙ n t) = αₙ n t) :
    TendstoUniformlyOn (fun n t => F (βₙ n t)) α atTop I := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hFe := Metric.tendstoUniformlyOn_iff.mp hF (ε / 2) (by positivity)
  have hαe := Metric.tendstoUniformlyOn_iff.mp hα (ε / 2) (by positivity)
  filter_upwards [hFe, hαe] with n hnF hnα
  intro t ht
  have heF := hnF (βₙ n t) (hQ n ht)
  have heα := hnα t ht
  have heF' : dist (αₙ n t) (F (βₙ n t)) < ε / 2 := by
    rw [← hrelation n t ht, dist_comm]
    exact heF
  exact (dist_triangle (α t) (αₙ n t) (F (βₙ n t))).trans_lt
    (by linarith)

/-- The unique inverse guide is the uniform limit on a fixed interval.
The compact set can be supplied by `inverse_guide_family_compactness`. -/
theorem exists_unique_uniform_guide_limit
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (βₙ αₙ : ℕ → ℝ → ℂ) (α : ℝ → ℂ)
    {Q : Set ℂ} {I : Set ℝ} (hQ : IsCompact Q)
    (hFcont : ContinuousOn F Q) (hi : InjOn F Q)
    (hF : TendstoUniformlyOn Fₙ F atTop Q)
    (hα : TendstoUniformlyOn αₙ α atTop I)
    (hβQ : ∀ n, MapsTo (βₙ n) I Q)
    (hβcont : ∀ n, ContinuousOn (βₙ n) I)
    (hrelation : ∀ n t, t ∈ I → Fₙ n (βₙ n t) = αₙ n t) :
    ∃ β : ℝ → ℂ, MapsTo β I Q ∧ EqOn (F ∘ β) α I ∧ ContinuousOn β I ∧
      TendstoUniformlyOn βₙ β atTop I ∧
      ∀ β' : ℝ → ℂ, MapsTo β' I Q → EqOn (F ∘ β') α I → EqOn β' β I := by
  classical
  have hc := limiting_map_composition_tendsto Fₙ F βₙ αₙ α hF hα hβQ hrelation
  have hFQ : IsClosed (F '' Q) := (hQ.image_of_continuousOn hFcont).isClosed
  have hex : ∀ t ∈ I, ∃ z ∈ Q, F z = α t := by
    intro t ht
    have hlim := hc.tendsto_at ht
    have hm : α t ∈ F '' Q := hFQ.mem_of_tendsto hlim
      (Eventually.of_forall (fun n => mem_image_of_mem F (hβQ n ht)))
    exact hm
  choose b hbQ hbF using hex
  let β : ℝ → ℂ := fun t => if ht : t ∈ I then b t ht else 0
  have hβm : MapsTo β I Q := by
    intro t ht
    simpa only [β, dite_eq_left ht] using hbQ t ht
  have hβF : EqOn (F ∘ β) α I := by
    intro t ht
    simpa only [Function.comp_apply, β, dite_eq_left ht] using hbF t ht
  have hu : TendstoUniformlyOn βₙ β atTop I := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨η, hη, hinv⟩ := compact_inverse_modulus hQ hFcont hi ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc η hη] with n hn
    intro t ht
    apply hinv (β t) (hβm ht) (βₙ n t) (hβQ n ht)
    have hβFt : F (β t) = α t := hβF ht
    rw [hβFt]
    exact hn t ht
  refine ⟨β, hβm, hβF, hu.continuousOn (Frequently.of_forall hβcont), hu, ?_⟩
  intro β' hβ'm hβ'F t ht
  apply hi (hβ'm ht) (hβm ht)
  exact (hβ'F ht).trans (hβF ht).symm

theorem inverse_guide_injective
    {β α : ℝ → ℂ} {G : ℂ → ℂ} {I : Set ℝ}
    (hrelation : EqOn (G ∘ β) α I) (hα : InjOn α I) : InjOn β I := by
  intro s hs t ht he
  apply hα hs ht
  rw [← hrelation hs, ← hrelation ht]
  exact congrArg G he

/-- The upper-half-plane condition separates every positive-time point
from the starting point; injectivity of the physical guide separates the rest. -/
theorem inverse_guide_injective_with_tip
    {β α : ℝ → ℂ} {F : ℂ → ℂ} {T : ℝ}
    (hzero : β 0 = 0) (hH : MapsTo β (Ioc 0 T) upperHalfPlane)
    (hrelation : EqOn (F ∘ β) α (Ioc 0 T)) (hα : InjOn α (Ioc 0 T)) :
    InjOn β (Icc 0 T) := by
  have hnz : ∀ t ∈ Ioc 0 T, β t ≠ 0 := by
    intro t ht he
    have hh : 0 < (β t).im := hH ht
    simp only [he, Complex.zero_im, lt_self_iff_false] at hh
  intro s hs t ht he
  by_cases hs0 : s = 0
  · subst s
    by_contra ht0
    have htp : 0 < t := by rcases eq_or_lt_of_le ht.1 with he | he; exact False.elim (ht0 he); exact he
    exact hnz t ⟨htp, ht.2⟩ (he.symm.trans hzero)
  by_cases ht0 : t = 0
  · subst t
    have hsp : 0 < s := by rcases eq_or_lt_of_le hs.1 with he | he; exact False.elim (hs0 he.symm); exact he
    exact False.elim (hnz s ⟨hsp, hs.2⟩ (he.trans hzero))
  have hsp : 0 < s := by rcases eq_or_lt_of_le hs.1 with he | he; exact False.elim (hs0 he.symm); exact he
  have htp : 0 < t := by rcases eq_or_lt_of_le ht.1 with he | he; exact False.elim (ht0 he.symm); exact he
  exact inverse_guide_injective hrelation hα ⟨hsp, hs.2⟩ ⟨htp, ht.2⟩ he

/-- The fixed-interval inverse limit supplied by the actual normalized
hyperbolic-speed estimates. -/
theorem normalized_guide_limit
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (βₙ αₙ : ℕ → ℝ → ℂ) (α : ℝ → ℂ)
    {δ T tw K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (htw : tw ∈ Icc δ T)
    (hD : ∀ n t, t ∈ Icc δ T → DifferentiableAt ℝ (βₙ n) t)
    (hH : ∀ n t, t ∈ Icc δ T → 0 < (βₙ n t).im)
    (hv : ∀ n t, t ∈ Icc δ T → ‖deriv (βₙ n) t‖ ≤ K * (βₙ n t).im)
    (hway : ∀ n, ‖βₙ n tw‖ = 1) (hangle : ∀ n, s ≤ (βₙ n tw).im)
    (hFcont : ContinuousOn F upperHalfPlane) (hi : InjOn F upperHalfPlane)
    (hF : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (hα : TendstoUniformlyOn αₙ α atTop (Icc δ T))
    (hrelation : ∀ n t, t ∈ Icc δ T → Fₙ n (βₙ n t) = αₙ n t) :
    ∃ β : ℝ → ℂ, MapsTo β (Icc δ T) upperHalfPlane ∧
      EqOn (F ∘ β) α (Icc δ T) ∧ ContinuousOn β (Icc δ T) ∧
      TendstoUniformlyOn βₙ β atTop (Icc δ T) := by
  obtain ⟨hQ, hQH, hβQ, _⟩ :=
    HyperbolicGuideCompactness.family_compact_containment_equicontinuity
      βₙ hK hs htw hD hH hv hway hangle
  have hFH := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hQ).mp
    (hF.mono hQH)
  obtain ⟨β, hβ, hβF, hc, hu, _⟩ := exists_unique_uniform_guide_limit
    Fₙ F βₙ αₙ α hQ (hFcont.mono hQH) (hi.mono hQH) hFH hα hβQ
    (fun n => fun t ht => (hD n t ht).continuousAt.continuousWithinAt) hrelation
  exact ⟨β, fun t ht => hQH (hβ ht), hβF, hc, hu⟩

/-- A common tip modulus upgrades uniform convergence away from the tip to
uniform convergence on the closed time interval, including continuity at zero. -/
theorem uniform_limit_of_away_and_common_tip_modulus
    (βₙ : ℕ → ℝ → ℂ) (β : ℝ → ℂ) {T : ℝ}
    (hcont : ∀ n, ContinuousOn (βₙ n) (Icc 0 T)) (hzero : β 0 = 0)
    (haway : ∀ δ : ℝ, 0 < δ → δ ≤ T →
      TendstoUniformlyOn βₙ β atTop (Icc δ T))
    (htip : ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ T ∧
      ∀ n t, t ∈ Icc 0 h → ‖βₙ n t‖ < ε) :
    TendstoUniformlyOn βₙ β atTop (Icc 0 T) ∧ ContinuousOn β (Icc 0 T) := by
  have hu : TendstoUniformlyOn βₙ β atTop (Icc 0 T) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨h, hh, hhT, hsmall⟩ := htip (ε / 3) (by positivity)
    have hβsmall : ∀ t ∈ Icc 0 h, ‖β t‖ ≤ ε / 3 := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · subst t
        simpa only [hzero, norm_zero] using (show (0 : ℝ) ≤ ε / 3 by positivity)
      · exact le_of_tendsto ((haway t ht0 (ht.2.trans hhT)).tendsto_at
          (show t ∈ Icc t T from ⟨le_rfl, ht.2.trans hhT⟩)).norm
          (Eventually.of_forall fun n => (hsmall n t ht).le)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (haway h hh hhT) ε hε] with n hn
    intro t ht
    by_cases hth : h ≤ t
    · exact hn t ⟨hth, ht.2⟩
    · have ht' : t ∈ Icc 0 h := ⟨ht.1, (lt_of_not_ge hth).le⟩
      calc
        dist (β t) (βₙ n t) ≤ ‖β t‖ + ‖βₙ n t‖ := dist_le_norm_add_norm _ _
        _ < ε := by linarith [hβsmall t ht', hsmall n t ht']
  exact ⟨hu, hu.continuousOn (Frequently.of_forall hcont)⟩

/-- Compatible inverse limits on all positive compact time intervals give one
continuous guide starting at zero. The compact sets are the actual confinement
sets proved by `HyperbolicGuideCompactness`. -/
theorem exists_continuous_guide_limit
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (βₙ αₙ : ℕ → ℝ → ℂ) (α : ℝ → ℂ)
    {T : ℝ}
    (hFcont : ContinuousOn F upperHalfPlane) (hi : InjOn F upperHalfPlane)
    (hF : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (hα : TendstoUniformlyOn αₙ α atTop (Icc 0 T))
    (hcont : ∀ n, ContinuousOn (βₙ n) (Icc 0 T))
    (hcompact : ∀ δ : ℝ, 0 < δ → δ ≤ T →
      ∃ Q : Set ℂ, IsCompact Q ∧ Q ⊆ upperHalfPlane ∧
        ∀ n, MapsTo (βₙ n) (Icc δ T) Q)
    (hrelation : ∀ n t, t ∈ Ioc 0 T → Fₙ n (βₙ n t) = αₙ n t)
    (htip : ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ h ≤ T ∧
      ∀ n t, t ∈ Icc 0 h → ‖βₙ n t‖ < ε) :
    ∃ β : ℝ → ℂ, β 0 = 0 ∧ MapsTo β (Ioc 0 T) upperHalfPlane ∧
      EqOn (F ∘ β) α (Ioc 0 T) ∧ ContinuousOn β (Icc 0 T) ∧
      TendstoUniformlyOn βₙ β atTop (Icc 0 T) := by
  classical
  have hlocal (δ : ℝ) (hδ : 0 < δ) (hδT : δ ≤ T) :
      ∃ β : ℝ → ℂ, MapsTo β (Icc δ T) upperHalfPlane ∧
        EqOn (F ∘ β) α (Icc δ T) ∧ ContinuousOn β (Icc δ T) ∧
        TendstoUniformlyOn βₙ β atTop (Icc δ T) := by
    obtain ⟨Q, hQ, hQH, hβQ⟩ := hcompact δ hδ hδT
    have hsub : Icc δ T ⊆ Icc 0 T := Icc_subset_Icc hδ.le le_rfl
    obtain ⟨β, hβ, hβF, hc, hu, _⟩ := exists_unique_uniform_guide_limit
      Fₙ F βₙ αₙ α hQ (hFcont.mono hQH) (hi.mono hQH)
      ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hQ).mp (hF.mono hQH))
      (hα.mono hsub) hβQ (fun n => (hcont n).mono hsub)
      (fun n t ht => hrelation n t ⟨hδ.trans_le ht.1, ht.2⟩)
    exact ⟨β, fun t ht => hQH (hβ ht), hβF, hc, hu⟩
  have hex : ∀ t ∈ Ioc 0 T, ∃ z ∈ upperHalfPlane, F z = α t := by
    intro t ht
    obtain ⟨b, hb, hbF, _, _⟩ := hlocal t ht.1 ht.2
    exact ⟨b t, hb ⟨le_rfl, ht.2⟩, hbF ⟨le_rfl, ht.2⟩⟩
  choose b hbH hbF using hex
  let β : ℝ → ℂ := fun t => if ht : t ∈ Ioc 0 T then b t ht else 0
  have hβ0 : β 0 = 0 := by simp [β]
  have hβH : MapsTo β (Ioc 0 T) upperHalfPlane := by
    intro t ht
    simpa only [β, dite_eq_left ht] using hbH t ht
  have hβF : EqOn (F ∘ β) α (Ioc 0 T) := by
    intro t ht
    simpa only [Function.comp_apply, β, dite_eq_left ht] using hbF t ht
  have haway (δ : ℝ) (hδ : 0 < δ) (hδT : δ ≤ T) :
      TendstoUniformlyOn βₙ β atTop (Icc δ T) := by
    obtain ⟨b', hb', hb'F, _, hu⟩ := hlocal δ hδ hδT
    have heq : EqOn b' β (Icc δ T) := by
      intro t ht
      have ht' : t ∈ Ioc 0 T := ⟨hδ.trans_le ht.1, ht.2⟩
      apply hi (hb' ht) (hβH ht')
      exact (hb'F ht).trans (hβF ht').symm
    exact hu.congr_right heq
  obtain ⟨hu, hc⟩ := uniform_limit_of_away_and_common_tip_modulus
    βₙ β hcont hβ0 haway htip
  exact ⟨β, hβ0, hβH, hβF, hc, hu⟩

end SLEExactGauge.GuideLimitIdentification

end

end OAI
