import OAI.Probability.SLE.Geometry.WaypointDerivativeBounds
import OAI.Probability.SLE.Geometry.LipschitzGuideConfinement
import OAI.Probability.SLE.Geometry.UniformGuideCompactness
import OAI.Probability.SLE.Geometry.PhysicalGuideCompactness
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

/-!
Joint compactness of conformal charts and physical/parameter access guides.
The sole published input is the explicitly stated normalized univalent
normal-family theorem. Normalization and guide identification use proved
clearance, tip-collapse, and compact-inverse estimates.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge.GuideCompactness

/-- The weak omitted-value derivative estimate proves that a nondegenerate
locally uniform conformal limit still omits the limiting omitted value. -/
theorem limit_omits_tip
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ) (aₙ : ℕ → ℂ) (a : ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (ha : Tendsto aₙ atTop (𝓝 a))
    (homit : ∀ n, aₙ n ∉ Fₙ n '' upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0) :
    a ∉ F '' upperHalfPlane := by
  rintro ⟨z, hz, he⟩
  have hr : 0 < z.im := hz
  have hball : ball z z.im ⊆ upperHalfPlane := ball_subset_upperHalfPlane le_rfl
  have hbound n : z.im * ‖deriv (Fₙ n) z‖ ≤
      (128 * Real.pi) * ‖Fₙ n z - aₙ n‖ :=
    univalent_omitted_value_bound_ball hr ((hFn n).mono hball)
      ((hinj n).mono hball) (aₙ n) (fun hh => homit n (image_mono hball hh))
  have hd := ((hconv.deriv (Eventually.of_forall hFn) isOpen_upperHalfPlane).tendsto_at hz).norm
  have hv := ((hconv.tendsto_at hz).sub ha).norm
  have hb : z.im * ‖deriv F z‖ ≤ (128 * Real.pi) * ‖F z - a‖ :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hd)
      (tendsto_const_nhds.mul hv) (Eventually.of_forall hbound)
  rw [he, sub_self, norm_zero, mul_zero] at hb
  have hp : 0 < z.im * ‖deriv F z‖ := mul_pos hr (norm_pos_iff.mpr (hne z hz))
  exact (not_le_of_gt hp) hb

/-- Reindexing a locally uniform limit along a subsequence. -/
theorem locallyUniform_subsequence
    {Fₙ : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {S : Set ℂ}
    (h : TendstoLocallyUniformlyOn Fₙ F atTop S)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    TendstoLocallyUniformlyOn (fun n => Fₙ (φ n)) F atTop S := by
  intro U hU z hz
  obtain ⟨V, hV, he⟩ := h U hU z hz
  exact ⟨V, hV, hφ.tendsto_atTop.eventually he⟩

/-- The unit-semicircle waypoint normalization survives uniform guide
convergence on the closed time interval. -/
theorem normalized_waypoint_of_uniform_limit
    {βₙ : ℕ → ℝ → ℂ} {β : ℝ → ℂ} {I : Set ℝ} {tw s : ℝ}
    (hu : TendstoUniformlyOn βₙ β atTop I) (htw : tw ∈ I)
    (hway : ∀ n, ‖βₙ n tw‖ = 1 ∧ s ≤ (βₙ n tw).im) :
    ‖β tw‖ = 1 ∧ s ≤ (β tw).im := by
  have hn := (hu.tendsto_at htw).norm
  have hn' : Tendsto (fun n : ℕ => ‖βₙ n tw‖) atTop (𝓝 (1 : ℝ)) := by
    have he : (fun n : ℕ => ‖βₙ n tw‖) = fun _ => (1 : ℝ) :=
      funext (fun n => (hway n).1)
    rw [he]
    exact tendsto_const_nhds
  exact ⟨tendsto_nhds_unique hn hn',
    ge_of_tendsto (Complex.continuous_im.continuousAt.tendsto.comp (hu.tendsto_at htw))
      (Eventually.of_forall fun n => (hway n).2)⟩

/-- Physical clearance on every interval away from zero gives the compact
parameter confinement required to identify the inverse-guide limit. -/
theorem compact_parameter_family_of_clearance
    (g : ℕ → ℂ → ℂ) (D : ℕ → Set ℂ) (αₙ βₙ : ℕ → ℝ → ℂ)
    {T tw s : ℝ} (C : ℝ≥0) (htw : 0 < tw) (htwT : tw ≤ T) (hs : 0 < s)
    (hαL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 T))
    (hg : ∀ n, DifferentiableOn ℂ (g n) (D n)) (hig : ∀ n, InjOn (g n) (D n))
    (hgH : ∀ n, MapsTo (g n) (D n) upperHalfPlane)
    (hway : ∀ n, ‖βₙ n tw‖ = 1 ∧ s ≤ (βₙ n tw).im)
    (hβeq : ∀ n t, t ∈ Ioc 0 T → βₙ n t = g n (αₙ n t))
    (hclear : ∀ δ : ℝ, 0 < δ → δ ≤ T → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ T → ball (αₙ n t) r ⊆ D n) :
    ∀ δ : ℝ, 0 < δ → δ ≤ T →
      ∃ Q : Set ℂ, IsCompact Q ∧ Q ⊆ upperHalfPlane ∧
        ∀ n, MapsTo (βₙ n) (Icc δ T) Q := by
  intro δ hδ hδT
  let δ' := min δ tw
  have hδ' : 0 < δ' := lt_min hδ htw
  have hδ'T : δ' ≤ T := (min_le_left _ _).trans hδT
  have htw' : tw ∈ Icc δ' T := ⟨min_le_right _ _, htwT⟩
  have hsub : Icc δ' T ⊆ Icc 0 T := Icc_subset_Icc hδ'.le le_rfl
  obtain ⟨r, hr, hballs⟩ := hclear δ' hδ' hδ'T
  obtain ⟨Q, hQ, hQH, hmap, _⟩ :=
    LipschitzGuideConfinement.family_compact_containment g αₙ hr C hs htw'
      (fun n => (hαL n).mono hsub)
      (fun n t ht => (hg n).mono (hballs n t ht))
      (fun n t ht => (hig n).mono (hballs n t ht))
      (fun n t ht => (hgH n).mono_left (hballs n t ht))
      (fun n => by rw [← hβeq n tw ⟨htw, htwT⟩]; exact (hway n).1)
      (fun n => by rw [← hβeq n tw ⟨htw, htwT⟩]; exact (hway n).2)
  refine ⟨Q, hQ, hQH, ?_⟩
  intro n t ht
  rw [hβeq n t ⟨hδ.trans_le ht.1, ht.2⟩]
  exact hmap n ⟨(min_le_left δ tw).trans ht.1, ht.2⟩

/-- Actual inverse charts with a common physical clearance at the waypoint,
bi-Lipschitz physical guides, and compact parameter confinement have one
joint subsequential limit. The inverse guide remains continuous and simple
through its initial boundary point. -/
theorem exists_joint_guide_limit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hpublished : PublishedHalfPlaneUnivalentCompactness)
    (Fₙ g : ℕ → ℂ → ℂ) (D : ℕ → Set ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ)
    (αₙ βₙ : ℕ → ℝ → ℂ) (aₙ : ℕ → ℂ)
    {T tw s ρ A c : ℝ} (C : ℝ≥0)
    (hT : 0 < T) (htw : 0 < tw) (htwT : tw ≤ T)
    (hs : 0 < s) (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 < (C : ℝ))
    (hD : ∀ n, IsOpen (D n))
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hiFn : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hg : ∀ n, DifferentiableOn ℂ (g n) (D n)) (hig : ∀ n, InjOn (g n) (D n))
    (hFD : ∀ n, MapsTo (Fₙ n) upperHalfPlane (D n))
    (hgH : ∀ n, MapsTo (g n) (D n) upperHalfPlane)
    (hgf : ∀ n z, z ∈ upperHalfPlane → g n (Fₙ n z) = z)
    (hbar : ∀ n, ContinuousOn (Fbar n) {z : ℂ | 0 ≤ z.im})
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (Fₙ n z : OnePoint ℂ))
    (hαL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 T))
    (hα0 : ∀ n, αₙ n 0 = aₙ n) (haBound : ∀ n, ‖aₙ n‖ ≤ A)
    (hchord : ∀ n u, u ∈ Icc 0 T → ∀ v, v ∈ Icc 0 T →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hβ : ∀ n, ContinuousOn (βₙ n) (Icc 0 T)) (hβ0 : ∀ n, βₙ n 0 = 0)
    (hβH : ∀ n t, t ∈ Icc 0 T → 0 ≤ (βₙ n t).im)
    (hway : ∀ n, ‖βₙ n tw‖ = 1 ∧ s ≤ (βₙ n tw).im)
    (hclear : ∀ n, ball (αₙ n tw) ρ ⊆ D n)
    (homit : ∀ n, aₙ n ∉ Fₙ n '' upperHalfPlane)
    (hrelation : ∀ n t, t ∈ Ioc 0 T → Fₙ n (βₙ n t) = αₙ n t)
    (hbarRelation : ∀ n t, t ∈ Icc 0 T → Fbar n (βₙ n t) = (αₙ n t : OnePoint ℂ))
    (hcompact : ∀ δ : ℝ, 0 < δ → δ ≤ T →
      ∃ Q : Set ℂ, IsCompact Q ∧ Q ⊆ upperHalfPlane ∧
        ∀ n, MapsTo (βₙ n) (Icc δ T) Q) :
    ∃ (φ : ℕ → ℕ) (F : ℂ → ℂ) (α β : ℝ → ℂ), StrictMono φ ∧
      DifferentiableOn ℂ F upperHalfPlane ∧ InjOn F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, deriv F z ≠ 0) ∧ α 0 ∉ F '' upperHalfPlane ∧
      TendstoLocallyUniformlyOn (fun n => Fₙ (φ n)) F atTop upperHalfPlane ∧
      TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun n => βₙ (φ n)) β atTop (Icc 0 T) ∧
      Tendsto (fun n => aₙ (φ n)) atTop (𝓝 (α 0)) ∧
      LipschitzOnWith C α (Icc 0 T) ∧ ContinuousOn α (Icc 0 T) ∧ InjOn α (Icc 0 T) ∧
      β 0 = 0 ∧ ContinuousOn β (Icc 0 T) ∧ InjOn β (Icc 0 T) ∧
      MapsTo β (Ioc 0 T) upperHalfPlane ∧ EqOn (F ∘ β) α (Ioc 0 T) := by
  have htwi : tw ∈ Icc (0 : ℝ) T := ⟨htw.le, htwT⟩
  have hnear n : ‖Fₙ n (βₙ n tw) - aₙ n‖ ≤ (C : ℝ) * tw := by
    rw [hrelation n tw ⟨htw, htwT⟩, ← hα0 n, ← dist_eq_norm]
    have hh := (hαL n).dist_le_mul tw htwi 0 ⟨le_rfl, hT.le⟩
    simpa only [Real.dist_eq, sub_zero, abs_of_pos htw] using hh
  obtain ⟨m, M, hm, hvalue, hder, hatip⟩ := waypoint_family_normalization_of_clearance
    Fₙ g D hD hFn hiFn hg hig hFD hgH hgf (fun n => βₙ n tw) aₙ s ρ
    ((C : ℝ) * tw) A hs hρ hway
    (fun n => by rw [hrelation n tw ⟨htw, htwT⟩]; exact hclear n) homit hnear haBound
  have himage n t (ht : t ∈ Icc 0 T) : ∃ w : ℂ,
      Fbar n (βₙ n t) = (w : OnePoint ℂ) ∧ ‖w - aₙ n‖ ≤ (C : ℝ) * t := by
    refine ⟨αₙ n t, hbarRelation n t ht, ?_⟩
    rw [← hα0 n, ← dist_eq_norm]
    have hh := (hαL n).dist_le_mul t ht 0 ⟨le_rfl, hT.le⟩
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg ht.1] using hh
  have htip := uniform_tip_collapse_of_published_compactness P κ hκ hκ8 γ hSLE
    hpublished Fₙ Fbar hFn hiFn hbar hext (fun n => βₙ n tw) aₙ s m M hs hm
    hway hvalue hder hatip βₙ T C hT hC hβ hβ0 hβH himage
  obtain ⟨φ₀, F, hφ₀, hF, hiF, hFne, hFconv⟩ :=
    hpublished Fₙ (fun n => βₙ n tw) s m M hs hm hFn hiFn hway hvalue hder
  obtain ⟨α, ψ, hψ, hαconv, hαLip, hαcont, _, _, hαinj⟩ :=
    PhysicalGuideCompactness.exists_simple_uniform_subsequence (fun n => αₙ (φ₀ n))
      hT.le C hc (fun n => hαL _) (fun n => by rw [hα0]; exact haBound _)
      (fun n => hchord _)
  let φ : ℕ → ℕ := φ₀ ∘ ψ
  have hφ : StrictMono φ := hφ₀.comp hψ
  have hFconv' : TendstoLocallyUniformlyOn (fun n => Fₙ (φ n)) F atTop upperHalfPlane :=
    locallyUniform_subsequence hFconv hψ
  have hαconv' : TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 T) := hαconv
  have halim : Tendsto (fun n => aₙ (φ n)) atTop (𝓝 (α 0)) := by
    simpa only [hα0] using hαconv'.tendsto_at (show 0 ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT.le⟩)
  have hlimomit : α 0 ∉ F '' upperHalfPlane := limit_omits_tip
    (fun n => Fₙ (φ n)) F (fun n => aₙ (φ n)) (α 0)
    (fun n => hFn _) (fun n => hiFn _) hFconv' halim (fun n => homit _) hFne
  obtain ⟨β, hβlim0, hβlimH, hβrel, hβcont, hβconv⟩ :=
    GuideLimitIdentification.exists_continuous_guide_limit
      (fun n => Fₙ (φ n)) F (fun n => βₙ (φ n)) (fun n => αₙ (φ n)) α
      hF.continuousOn hiF hFconv' hαconv' (fun n => hβ _)
      (fun δ hδ hδT => by
        obtain ⟨Q, hQ, hQH, hβQ⟩ := hcompact δ hδ hδT
        exact ⟨Q, hQ, hQH, fun n => hβQ _⟩)
      (fun n => hrelation _)
      (fun ε hε => by
        obtain ⟨h, hh, hhT, hb⟩ := htip ε hε
        exact ⟨h, hh, hhT, fun n => hb _⟩)
  have hβinj := GuideLimitIdentification.inverse_guide_injective_with_tip
    hβlim0 hβlimH hβrel (hαinj.mono Ioc_subset_Icc_self)
  exact ⟨φ, F, α, β, hφ, hF, hiF, hFne, hlimomit, hFconv', hαconv', hβconv,
    halim, hαLip, hαcont, hαinj, hβlim0, hβcont, hβinj, hβlimH, hβrel⟩

/-- Joint guide compactness with compact containment discharged by the
actual inverse charts and positive physical clearance away from the tip. -/
theorem exists_joint_guide_limit_of_clearance
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hpublished : PublishedHalfPlaneUnivalentCompactness)
    (Fₙ g : ℕ → ℂ → ℂ) (D : ℕ → Set ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ)
    (αₙ βₙ : ℕ → ℝ → ℂ) (aₙ : ℕ → ℂ)
    {T tw s ρ A c : ℝ} (C : ℝ≥0)
    (hT : 0 < T) (htw : 0 < tw) (htwT : tw ≤ T)
    (hs : 0 < s) (hρ : 0 < ρ) (hc : 0 < c) (hC : 0 < (C : ℝ))
    (hD : ∀ n, IsOpen (D n))
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hiFn : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hg : ∀ n, DifferentiableOn ℂ (g n) (D n)) (hig : ∀ n, InjOn (g n) (D n))
    (hFD : ∀ n, MapsTo (Fₙ n) upperHalfPlane (D n))
    (hgH : ∀ n, MapsTo (g n) (D n) upperHalfPlane)
    (hgf : ∀ n z, z ∈ upperHalfPlane → g n (Fₙ n z) = z)
    (hbar : ∀ n, ContinuousOn (Fbar n) {z : ℂ | 0 ≤ z.im})
    (hext : ∀ n z, z ∈ upperHalfPlane → Fbar n z = (Fₙ n z : OnePoint ℂ))
    (hαL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 T))
    (hα0 : ∀ n, αₙ n 0 = aₙ n) (haBound : ∀ n, ‖aₙ n‖ ≤ A)
    (hchord : ∀ n u, u ∈ Icc 0 T → ∀ v, v ∈ Icc 0 T →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hβ : ∀ n, ContinuousOn (βₙ n) (Icc 0 T)) (hβ0 : ∀ n, βₙ n 0 = 0)
    (hβH : ∀ n t, t ∈ Icc 0 T → 0 ≤ (βₙ n t).im)
    (hway : ∀ n, ‖βₙ n tw‖ = 1 ∧ s ≤ (βₙ n tw).im)
    (hclear : ∀ n, ball (αₙ n tw) ρ ⊆ D n)
    (homit : ∀ n, aₙ n ∉ Fₙ n '' upperHalfPlane)
    (hrelation : ∀ n t, t ∈ Ioc 0 T → Fₙ n (βₙ n t) = αₙ n t)
    (hbarRelation : ∀ n t, t ∈ Icc 0 T → Fbar n (βₙ n t) = (αₙ n t : OnePoint ℂ))
    (hβeq : ∀ n t, t ∈ Ioc 0 T → βₙ n t = g n (αₙ n t))
    (hclearAway : ∀ δ : ℝ, 0 < δ → δ ≤ T → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ T → ball (αₙ n t) r ⊆ D n) :
    ∃ (φ : ℕ → ℕ) (F : ℂ → ℂ) (α β : ℝ → ℂ), StrictMono φ ∧
      DifferentiableOn ℂ F upperHalfPlane ∧ InjOn F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, deriv F z ≠ 0) ∧ α 0 ∉ F '' upperHalfPlane ∧
      TendstoLocallyUniformlyOn (fun n => Fₙ (φ n)) F atTop upperHalfPlane ∧
      TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 T) ∧
      TendstoUniformlyOn (fun n => βₙ (φ n)) β atTop (Icc 0 T) ∧
      Tendsto (fun n => aₙ (φ n)) atTop (𝓝 (α 0)) ∧
      LipschitzOnWith C α (Icc 0 T) ∧ ContinuousOn α (Icc 0 T) ∧ InjOn α (Icc 0 T) ∧
      β 0 = 0 ∧ ContinuousOn β (Icc 0 T) ∧ InjOn β (Icc 0 T) ∧
      MapsTo β (Ioc 0 T) upperHalfPlane ∧ EqOn (F ∘ β) α (Ioc 0 T) := by
  have hcompact := compact_parameter_family_of_clearance g D αₙ βₙ C htw htwT hs
    hαL hg hig hgH hway hβeq hclearAway
  exact exists_joint_guide_limit P κ hκ hκ8 γ hSLE hpublished Fₙ g D Fbar αₙ βₙ aₙ C
    hT htw htwT hs hρ hc hC hD hFn hiFn hg hig hFD hgH hgf hbar hext hαL hα0 haBound
    hchord hβ hβ0 hβH hway hclear homit hrelation hbarRelation hcompact

end SLEExactGauge.GuideCompactness

end

end OAI
