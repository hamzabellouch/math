import OAI.Probability.SLE.Gauge.RetainedTubeSausage

namespace OAI

/-! Physical middle-strip margins are chosen separately for each retained
compact set. A finite probability retention then permits their finite union;
no inclusion of the entire limiting open strip in every moving strip is used. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RetainedTubeSausage

/-- Each compact subset of the limiting middle strip has one open physical
neighborhood lying in every sufficiently late moving middle strip. -/
theorem eventual_middle_neighborhood
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (K : Set ℂ) (hK : IsCompact K)
    (hband : K ⊆ U ∩ {z | (1 / 3 : ℝ) < p z ∧ p z < 2 / 3}) :
    ∃ R : Set ℂ, IsOpen R ∧ K ⊆ R ∧
      ∀ᶠ n in atTop, R ⊆ U ∩ {z | (1 / 3 : ℝ) < pₙ n z ∧ pₙ n z < 2 / 3} := by
  let V := U ∩ p ⁻¹' Ioo (1 / 3 : ℝ) (2 / 3)
  have hV : IsOpen V := hp.isOpen_inter_preimage hU isOpen_Ioo
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_cthickening_subset_open hV hband
  let C := cthickening δ K
  let R := thickening δ K
  have hC : IsCompact C := hK.cthickening
  have hCU : C ⊆ U := hthick.trans inter_subset_left
  have hCR : R ⊆ C := thickening_subset_cthickening δ K
  have hpC : IsCompact (p '' C) := hC.image_of_continuousOn (hp.mono hCU)
  have hpband : p '' C ⊆ Ioo (1 / 3 : ℝ) (2 / 3) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hthick hz).2
  obtain ⟨ε, hε, heps⟩ := hpC.exists_thickening_subset_open isOpen_Ioo hpband
  have hu : TendstoUniformlyOn pₙ p atTop C :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hC).mp (hconv.mono hCU)
  refine ⟨R, isOpen_thickening, self_subset_thickening hδ K, ?_⟩
  filter_upwards [hu _ (Metric.dist_mem_uniformity hε)] with n hn
  intro z hz
  have hzC := hCR hz
  refine ⟨hCU hzC, heps ?_⟩
  exact mem_thickening_iff.mpr ⟨p z, mem_image_of_mem p hzC,
    by simpa only [dist_comm] using hn z hzC⟩

/-- Finite retention permits compact-dependent physical neighborhoods. -/
theorem countable_stopped_mass_ae_window_compact_regions
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : ℕ → Set ℂ) (hK : ∀ i, IsCompact (K i)) (hKH : ∀ i, K i ⊆ upperHalfPlane)
    (R : ℕ → Set ℂ) (hR : ∀ i, IsOpen (R i)) (himage : ∀ i, F '' K i ⊆ R i)
    (J : ℕ → ℝ≥0 × ℝ≥0) (hJ : ∀ i, (J i).1 < (J i).2)
    (E : Set Ω) (D : ℕ → Set Ω) (hE : MeasurableSet E) (hD : ∀ i, MeasurableSet (D i))
    (hcover : P (E \ ⋃ i, D i) = 0)
    (hretain : ∀ i ω, ω ∈ D i → γ ω '' Icc (J i).1 (J i).2 ⊆ K i)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (s t : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ i, ∀ᶠ n in atTop, R i ⊆ Rₙ n)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n ∩ E))
    (hwindow : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E ∩ D i →
      s n ω ≤ (J i).1 ∧ (J i).2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc (J i).1 (J i).2)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 4) ≤ P {ω | ω ∈ G n ∩ E ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (s n ω) (t n ω) (v n) (Rₙ n)} := by
  classical
  obtain ⟨N, hsmall⟩ := finite_retention_of_countable_cover P E D hE hD hcover
    (ENNReal.ofReal (q / 2)) (ENNReal.ofReal_pos.mpr (by positivity))
  have hN : ∀ᶠ n in atTop, ENNReal.ofReal (q / 2) ≤
      P (G n ∩ E ∩ ⋃ i ∈ Finset.range N, D i) := by
    filter_upwards [hG] with n hn
    let A := ⋃ i ∈ Finset.range N, D i
    have hsub : G n ∩ E ⊆ (G n ∩ E ∩ A) ∪ (E \ A) := by
      intro ω hω
      by_cases hA : ω ∈ A
      · exact Or.inl ⟨hω, hA⟩
      · exact Or.inr ⟨hω.2, hA⟩
    have hb := hn.trans ((measure_mono hsub).trans (measure_union_le _ _))
    by_contra h
    have he : ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) =
        ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    exact (not_lt_of_ge hb) (he ▸ ENNReal.add_lt_add (lt_of_not_ge h) hsmall)
  let A := ⋃ i ∈ Finset.range N, D i
  let Q := ⋃ i ∈ Finset.range N, K i
  let H : ℕ → Set Ω := fun n => G n ∩ E ∩ A
  let R₀ : Set ℂ := ⋃ i ∈ Finset.range N, R i
  have hR₀ : IsOpen R₀ := isOpen_iUnion fun i => isOpen_iUnion fun _ => hR i
  have hregion₀ : ∀ᶠ n in atTop, R₀ ⊆ Rₙ n := by
    have hf := (Finset.eventually_all (Finset.range N)).mpr (fun i _ => hregion i)
    filter_upwards [hf] with n hn
    exact iUnion₂_subset (fun i hi => hn i hi)
  have hQ : IsCompact Q := (Finset.range N).isCompact_biUnion (fun i _ => hK i)
  have hQH : Q ⊆ upperHalfPlane := iUnion₂_subset (fun i _ => hKH i)
  have hQR : F '' Q ⊆ R₀ := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨i, hiN, hi⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨i, hiN, himage i (mem_image_of_mem F hi)⟩
  have hQn : Q.Nonempty := by
    obtain ⟨n, hn⟩ := hN.exists
    have hHpos : 0 < P (H n) :=
      (ENNReal.ofReal_pos.mpr (by positivity : 0 < q / 2)).trans_le hn
    obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hHpos.ne'
    obtain ⟨i, hi, hDi⟩ := mem_iUnion₂.mp hω.2
    exact ⟨γ ω (J i).1, mem_iUnion₂.mpr ⟨i, hi,
      hretain i ω hDi (mem_image_of_mem (γ ω) ⟨le_rfl, (hJ i).le⟩)⟩⟩
  let I := (Finset.range N).image J
  have hI : ∀ L ∈ I, L.1 < L.2 := by
    intro L hL
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hL
    exact hJ i
  have hwin : ∀ᶠ n in atTop, ∀ i ∈ Finset.range N, ∀ᵐ ω ∂P, ω ∈ G n ∩ E ∩ D i →
      s n ω ≤ (J i).1 ∧ (J i).2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc (J i).1 (J i).2) :=
    (Finset.eventually_all _).mpr (fun i _ => hwindow i)
  have hr : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ H n →
      ∃ L ∈ I, γ ω '' Icc L.1 L.2 ⊆ Q ∧ s n ω ≤ L.1 ∧ L.2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc L.1 L.2) := by
    filter_upwards [hwin] with n hn
    filter_upwards [(Finset.eventually_all _).mpr hn] with ω hω
    intro hH
    obtain ⟨i, hi, hDi⟩ := mem_iUnion₂.mp hH.2
    exact ⟨J i, Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      (hretain i ω hDi).trans (subset_iUnion₂_of_subset i hi Subset.rfl),
      hω i hi ⟨hH.1, hDi⟩⟩
  obtain ⟨a, ha, hmass⟩ := compact_conformal_stopped_passage_mass_ae P κ hκ hκ8 γ hSLE
    Fₙ F hFn hinj hF hne hconv Q hQ hQn hQH R₀ hR₀ hQR I hI v hv hlim
    η s t Rₙ H (q / 2) (by positivity) hN hregion₀ hr
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmass] with n hn
  have hqq : q / 2 / 2 = q / 4 := by ring
  rw [hqq] at hn
  exact hn.trans (measure_mono (fun _ hω => ⟨hω.1.1, hω.2⟩))

/-- Local coordinate convergence supplies the compact-dependent physical
margins needed by the retained stopped-mass theorem. -/
theorem countable_stopped_mass_ae_window_middle_regions
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : ℕ → Set ℂ) (hK : ∀ i, IsCompact (K i)) (hKH : ∀ i, K i ⊆ upperHalfPlane)
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (himage : ∀ i, F '' K i ⊆ U ∩ {z | (1 / 3 : ℝ) < p z ∧ p z < 2 / 3})
    (J : ℕ → ℝ≥0 × ℝ≥0) (hJ : ∀ i, (J i).1 < (J i).2)
    (E : Set Ω) (D : ℕ → Set Ω) (hE : MeasurableSet E) (hD : ∀ i, MeasurableSet (D i))
    (hcover : P (E \ ⋃ i, D i) = 0)
    (hretain : ∀ i ω, ω ∈ D i → γ ω '' Icc (J i).1 (J i).2 ⊆ K i)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (s t : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ᶠ n in atTop, U ∩ {z | (1 / 3 : ℝ) < pₙ n z ∧ pₙ n z < 2 / 3} ⊆ Rₙ n)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n ∩ E))
    (hwindow : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E ∩ D i →
      s n ω ≤ (J i).1 ∧ (J i).2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc (J i).1 (J i).2)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 4) ≤ P {ω | ω ∈ G n ∩ E ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (s n ω) (t n ω) (v n) (Rₙ n)} := by
  have hneighborhood (i : ℕ) := eventual_middle_neighborhood pₙ p U hU hp hpconv
    (F '' K i) ((hK i).image_of_continuousOn (hF.continuousOn.mono (hKH i))) (himage i)
  choose R hR himageR hRlate using hneighborhood
  apply countable_stopped_mass_ae_window_compact_regions P κ hκ hκ8 γ hSLE
    Fₙ F hFn hinj hF hne hconv K hK hKH R hR himageR J hJ E D hE hD hcover hretain
    v hv hlim η s t Rₙ ?_ G q hq hG hwindow
  intro i
  filter_upwards [hRlate i, hregion] with n hn htarget
  exact hn.trans htarget

end SLEExactGauge.RetainedTubeSausage

end

end OAI
