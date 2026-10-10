import OAI.Probability.SLE.Gauge.PassageRetention
import OAI.Probability.SLE.Mass.StoppedConformalPassageMass

namespace OAI

/-! Actual open-tube passage certificates imply a positive stopped sausage
mass. The retained time window is derived from the front coordinate, rather
than supplied as a separate geometric hypothesis. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RetainedTubeSausage
open PassageRetention

/-- Uniformly convergent physical coordinates preserve a strict front bound
on each compact retained parameter set. -/
theorem eventually_front_lt_on_compact
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hF : ContinuousOn F upperHalfPlane)
    (hFconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (hKU : F '' K ⊆ U) (q : ℝ) (hbound : ∀ z ∈ K, p (F z) < q) :
    ∀ᶠ n in atTop, ∀ z ∈ K, pₙ n (Fₙ n z) < q := by
  by_cases hKn : K.Nonempty
  · let V := U ∩ p ⁻¹' Iio q
    have hV : IsOpen V := hp.isOpen_inter_preimage hU isOpen_Iio
    have hFK : IsCompact (F '' K) := hK.image_of_continuousOn (hF.mono hKH)
    have hFKV : F '' K ⊆ V := by
      rintro w ⟨z, hz, rfl⟩
      exact ⟨hKU (mem_image_of_mem F hz), hbound z hz⟩
    obtain ⟨δ, hδ, hthick⟩ := hFK.exists_cthickening_subset_open hV hFKV
    let L := cthickening (δ / 2) (F '' K)
    have hL : IsCompact L := hFK.cthickening
    have hLV : L ⊆ V := (cthickening_mono (by linarith) (F '' K)).trans hthick
    have hLn : L.Nonempty := (hKn.image F).mono (self_subset_cthickening _)
    have hpL : ContinuousOn p L := hp.mono (hLV.trans inter_subset_left)
    obtain ⟨z₀, hz₀, hmax⟩ := hL.exists_isMaxOn hLn hpL
    have hz₀q : p z₀ < q := (hLV hz₀).2
    have huF : TendstoUniformlyOn Fₙ F atTop K :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp (hFconv.mono hKH)
    have huP : TendstoUniformlyOn pₙ p atTop L :=
      (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hL).mp
        (hpconv.mono (hLV.trans inter_subset_left))
    filter_upwards [huF _ (Metric.dist_mem_uniformity (by positivity : 0 < δ / 2)),
      huP _ (Metric.dist_mem_uniformity (sub_pos.mpr hz₀q))] with n hnF hnP
    intro z hz
    have hzL : Fₙ n z ∈ L :=
      mem_cthickening_of_dist_le _ (F z) (δ / 2) (F '' K)
        (mem_image_of_mem F hz) (by simpa only [dist_comm] using (hnF z hz).le)
    have hdiff := hnP (Fₙ n z) hzL
    have hupper : p (Fₙ n z) ≤ p z₀ := hmax hzL
    rw [Real.dist_eq] at hdiff
    have hh := (abs_lt.mp hdiff).1
    linarith
  · have hKe : K = ∅ := not_nonempty_iff_eq_empty.mp hKn
    simp only [hKe, mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
      eventually_true]

/-- The countable stopped-mass reduction also permits almost-sure window
and chart identities, as supplied by the actual boundary restart. -/
theorem countable_stopped_mass_ae_window
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
    (R : Set ℂ) (hR : IsOpen R) (himage : ∀ i, F '' K i ⊆ R)
    (J : ℕ → ℝ≥0 × ℝ≥0) (hJ : ∀ i, (J i).1 < (J i).2)
    (E : Set Ω) (D : ℕ → Set Ω) (hE : MeasurableSet E) (hD : ∀ i, MeasurableSet (D i))
    (hcover : P (E \ ⋃ i, D i) = 0)
    (hretain : ∀ i ω, ω ∈ D i → γ ω '' Icc (J i).1 (J i).2 ⊆ K i)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (s t : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ n, ENNReal.ofReal q ≤ P (G n ∩ E))
    (hwindow : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E ∩ D i →
      s n ω ≤ (J i).1 ∧ (J i).2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc (J i).1 (J i).2)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 4) ≤ P {ω | ω ∈ G n ∩ E ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (s n ω) (t n ω) (v n) (Rₙ n)} := by
  classical
  obtain ⟨N, hN⟩ := varying_events_after_finite_retention P E D G hE hD hcover q hq hG
  let A := ⋃ i ∈ Finset.range N, D i
  let Q := ⋃ i ∈ Finset.range N, K i
  let H : ℕ → Set Ω := fun n => G n ∩ E ∩ A
  have hQ : IsCompact Q := (Finset.range N).isCompact_biUnion (fun i _ => hK i)
  have hQH : Q ⊆ upperHalfPlane := iUnion₂_subset (fun i _ => hKH i)
  have hQR : F '' Q ⊆ R := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hz
    exact himage i (mem_image_of_mem F hi)
  have hQn : Q.Nonempty := by
    have hHpos : 0 < P (H 0) := (ENNReal.ofReal_pos.mpr (by positivity : 0 < q / 2)).trans_le (hN 0)
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
    Fₙ F hFn hinj hF hne hconv Q hQ hQn hQH R hR hQR I hI v hv hlim
    η s t Rₙ H (q / 2) (by positivity) (Eventually.of_forall hN) hregion hr
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmass] with n hn
  have hqq : q / 2 / 2 = q / 4 := by ring
  rw [hqq] at hn
  exact hn.trans (measure_mono (fun _ hω => ⟨hω.1.1, hω.2⟩))

/-- The countable stopped-mass reduction also permits almost-sure window
and chart identities, as supplied by the actual boundary restart. -/
theorem countable_stopped_mass_ae_window_eventually
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
    (R : Set ℂ) (hR : IsOpen R) (himage : ∀ i, F '' K i ⊆ R)
    (J : ℕ → ℝ≥0 × ℝ≥0) (hJ : ∀ i, (J i).1 < (J i).2)
    (E : Set Ω) (D : ℕ → Set Ω) (hE : MeasurableSet E) (hD : ∀ i, MeasurableSet (D i))
    (hcover : P (E \ ⋃ i, D i) = 0)
    (hretain : ∀ i ω, ω ∈ D i → γ ω '' Icc (J i).1 (J i).2 ⊆ K i)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (s t : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
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
  have hQ : IsCompact Q := (Finset.range N).isCompact_biUnion (fun i _ => hK i)
  have hQH : Q ⊆ upperHalfPlane := iUnion₂_subset (fun i _ => hKH i)
  have hQR : F '' Q ⊆ R := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hz
    exact himage i (mem_image_of_mem F hi)
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
    Fₙ F hFn hinj hF hne hconv Q hQ hQn hQH R hR hQR I hI v hv hlim
    η s t Rₙ H (q / 2) (by positivity) hN hregion hr
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmass] with n hn
  have hqq : q / 2 / 2 = q / 4 := by ring
  rw [hqq] at hn
  exact hn.trans (measure_mono (fun _ hω => ⟨hω.1.1, hω.2⟩))

/-- Actual tube passages produce retained sausage mass before the varying
front stop. Compact intervals and stop windows are both derived here. -/
theorem retained_tube_stopped_sausage_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (hSLE : IsOrdinaryChordalSLE κ (fun ω => f ω) P)
    (σ : Ω → ℝ≥0) (hσ : Measurable σ)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (O W : Set ℂ) (hO : IsOpen O) (hOH : O ⊆ upperHalfPlane)
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (hFOU : MapsTo F O U) (hW : W ⊆ {z | 1 < p (F z)})
    (E : Set Ω) (hE : MeasurableSet E)
    (htube : E ⊆ stoppedPhysicalTube (fun ω => f ω) σ O W)
    (hstart : ∀ ω ∈ E, p (F (f ω (σ ω))) < 1 / 3)
    (R : Set ℂ) (hR : IsOpen R)
    (hmiddle : ∀ z ∈ O, 1 / 3 < p (F z) → p (F z) < 2 / 3 → F z ∈ R)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (τ : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ n, ENNReal.ofReal q ≤ P (G n ∩ E))
    (hη : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω ≤ t → f ω t ∈ upperHalfPlane →
      η n ω t = Fₙ n (f ω t))
    (hτ : ∀ n, ∀ᵐ ω ∂P, ω ∈ G n ∩ E →
      σ ω ≤ τ n ω ∧ 2 / 3 ≤ pₙ n (η n ω (τ n ω))) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 4) ≤ P {ω | ω ∈ G n ∩ E ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (σ ω) (τ n ω) (v n) (Rₙ n)} := by
  let progress := fun z => p (F z)
  have hprogress : ContinuousOn progress O :=
    hp.comp (hF.continuousOn.mono hOH) hFOU
  obtain ⟨K, M, L, N, hK, hM, hL, hN, hDm, hcover⟩ :=
    stopped_tube_retained_cover f hf σ hσ O W hO hOH progress hprogress hW E htube hstart
  let D : ℕ → Set Ω := fun i => retainedPassageCertificate f σ K M L N
    (beyondFrontRegion O progress) (enumerateRetainedPassage i)
  let Q : ℕ → Set ℂ := fun i => M (enumerateRetainedPassage i).1.2.2.1
  let J : ℕ → ℝ≥0 × ℝ≥0 := fun i =>
    (intervalStart (enumerateRetainedPassage i).1, intervalEnd (enumerateRetainedPassage i).1)
  have hQ : ∀ i, IsCompact (Q i) := fun i => (hM _).1
  have hQH : ∀ i, Q i ⊆ upperHalfPlane := fun i z hz => hOH ((hM _).2 hz).1
  have hQR : ∀ i, F '' Q i ⊆ R := by
    rintro i _ ⟨z, hz, rfl⟩
    have hh := (hM _).2 hz
    exact hmiddle z hh.1 hh.2.1 hh.2.2
  have hJ : ∀ i, (J i).1 < (J i).2 := fun i => intervalStart_lt_end _
  have hD : ∀ i, MeasurableSet (D i) := fun i => hDm _
  have hnull : P (E \ ⋃ i, D i) = 0 := by
    rw [sdiff_eq_empty.mpr (nat_retained_cover f σ K M L N _ E hcover), measure_empty]
  have hretain : ∀ i ω, ω ∈ D i →
      (fun t => f ω t) '' Icc (J i).1 (J i).2 ⊆ Q i := by
    intro i ω hω
    exact hω.1.2.2.2.1.image_subset
  have hwindow : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E ∩ D i →
      σ ω ≤ (J i).1 ∧ (J i).2 ≤ τ n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (f ω u)) (Icc (J i).1 (J i).2) := by
    intro i
    let j := enumerateRetainedPassage i
    have hLH : L j.1.2.2.2 ⊆ upperHalfPlane := fun z hz => hOH ((hL _).2 hz).1
    have hLU : F '' L j.1.2.2.2 ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFOU ((hL _).2 hz).1
    have hlt := eventually_front_lt_on_compact Fₙ F hF.continuousOn hconv pₙ p U hU hp hpconv
      (L j.1.2.2.2) (hL _).1 hLH hLU (2 / 3) (fun z hz => ((hL _).2 hz).2)
    filter_upwards [hlt] with n hn
    filter_upwards [hη n, hτ n] with ω hηω hτω
    intro hω
    have hDi : ω ∈ retainedPassageCertificate f σ K M L N
        (beyondFrontRegion O progress) j := hω.2
    obtain ⟨⟨hσs, _, _, hmid, hlow⟩, _⟩ := hDi
    have htau := hτω hω.1
    have hbefore : intervalEnd j.1 ≤ τ n ω := by
      by_contra hbad
      have hmem : f ω (τ n ω) ∈ L j.1.2.2.2 :=
        hlow.2 ⟨htau.1, (lt_of_not_ge hbad).le⟩
      have hh := hn _ hmem
      rw [← hηω (τ n ω) htau.1 (hLH hmem)] at hh
      exact (not_le_of_gt hh) htau.2
    refine ⟨hσs.le, hbefore, ?_⟩
    intro t ht
    exact hηω t (hσs.le.trans ht.1) (hOH ((hM _).2 (hmid ht)).1)
  exact countable_stopped_mass_ae_window P κ hκ hκ8 (fun ω => f ω) hSLE
    Fₙ F hFn hinj hF hne hconv Q hQ hQH R hR hQR J hJ E D hE hD hnull hretain
    v hv hlim η (fun _ => σ) τ Rₙ hregion G q hq hG hwindow
/-- Actual tube passages produce retained sausage mass before the varying
front stop. Compact intervals and stop windows are both derived here. -/
theorem retained_tube_stopped_sausage_mass_eventually
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (hSLE : IsOrdinaryChordalSLE κ (fun ω => f ω) P)
    (σ : Ω → ℝ≥0) (hσ : Measurable σ)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (O W : Set ℂ) (hO : IsOpen O) (hOH : O ⊆ upperHalfPlane)
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (hFOU : MapsTo F O U) (hW : W ⊆ {z | 1 < p (F z)})
    (E : Set Ω) (hE : MeasurableSet E)
    (htube : E ⊆ stoppedPhysicalTube (fun ω => f ω) σ O W)
    (hstart : ∀ ω ∈ E, p (F (f ω (σ ω))) < 1 / 3)
    (R : Set ℂ) (hR : IsOpen R)
    (hmiddle : ∀ z ∈ O, 1 / 3 < p (F z) → p (F z) < 2 / 3 → F z ∈ R)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (τ : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n ∩ E))
    (hη : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω ≤ t → f ω t ∈ upperHalfPlane →
      η n ω t = Fₙ n (f ω t))
    (hτ : ∀ n, ∀ᵐ ω ∂P, ω ∈ G n ∩ E →
      σ ω ≤ τ n ω ∧ 2 / 3 ≤ pₙ n (η n ω (τ n ω))) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 4) ≤ P {ω | ω ∈ G n ∩ E ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (σ ω) (τ n ω) (v n) (Rₙ n)} := by
  let progress := fun z => p (F z)
  have hprogress : ContinuousOn progress O :=
    hp.comp (hF.continuousOn.mono hOH) hFOU
  obtain ⟨K, M, L, N, hK, hM, hL, hN, hDm, hcover⟩ :=
    stopped_tube_retained_cover f hf σ hσ O W hO hOH progress hprogress hW E htube hstart
  let D : ℕ → Set Ω := fun i => retainedPassageCertificate f σ K M L N
    (beyondFrontRegion O progress) (enumerateRetainedPassage i)
  let Q : ℕ → Set ℂ := fun i => M (enumerateRetainedPassage i).1.2.2.1
  let J : ℕ → ℝ≥0 × ℝ≥0 := fun i =>
    (intervalStart (enumerateRetainedPassage i).1, intervalEnd (enumerateRetainedPassage i).1)
  have hQ : ∀ i, IsCompact (Q i) := fun i => (hM _).1
  have hQH : ∀ i, Q i ⊆ upperHalfPlane := fun i z hz => hOH ((hM _).2 hz).1
  have hQR : ∀ i, F '' Q i ⊆ R := by
    rintro i _ ⟨z, hz, rfl⟩
    have hh := (hM _).2 hz
    exact hmiddle z hh.1 hh.2.1 hh.2.2
  have hJ : ∀ i, (J i).1 < (J i).2 := fun i => intervalStart_lt_end _
  have hD : ∀ i, MeasurableSet (D i) := fun i => hDm _
  have hnull : P (E \ ⋃ i, D i) = 0 := by
    rw [sdiff_eq_empty.mpr (nat_retained_cover f σ K M L N _ E hcover), measure_empty]
  have hretain : ∀ i ω, ω ∈ D i →
      (fun t => f ω t) '' Icc (J i).1 (J i).2 ⊆ Q i := by
    intro i ω hω
    exact hω.1.2.2.2.1.image_subset
  have hwindow : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E ∩ D i →
      σ ω ≤ (J i).1 ∧ (J i).2 ≤ τ n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (f ω u)) (Icc (J i).1 (J i).2) := by
    intro i
    let j := enumerateRetainedPassage i
    have hLH : L j.1.2.2.2 ⊆ upperHalfPlane := fun z hz => hOH ((hL _).2 hz).1
    have hLU : F '' L j.1.2.2.2 ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFOU ((hL _).2 hz).1
    have hlt := eventually_front_lt_on_compact Fₙ F hF.continuousOn hconv pₙ p U hU hp hpconv
      (L j.1.2.2.2) (hL _).1 hLH hLU (2 / 3) (fun z hz => ((hL _).2 hz).2)
    filter_upwards [hlt] with n hn
    filter_upwards [hη n, hτ n] with ω hηω hτω
    intro hω
    have hDi : ω ∈ retainedPassageCertificate f σ K M L N
        (beyondFrontRegion O progress) j := hω.2
    obtain ⟨⟨hσs, _, _, hmid, hlow⟩, _⟩ := hDi
    have htau := hτω hω.1
    have hbefore : intervalEnd j.1 ≤ τ n ω := by
      by_contra hbad
      have hmem : f ω (τ n ω) ∈ L j.1.2.2.2 :=
        hlow.2 ⟨htau.1, (lt_of_not_ge hbad).le⟩
      have hh := hn _ hmem
      rw [← hηω (τ n ω) htau.1 (hLH hmem)] at hh
      exact (not_le_of_gt hh) htau.2
    refine ⟨hσs.le, hbefore, ?_⟩
    intro t ht
    exact hηω t (hσs.le.trans ht.1) (hOH ((hM _).2 (hmid ht)).1)
  exact countable_stopped_mass_ae_window_eventually P κ hκ hκ8 (fun ω => f ω) hSLE
    Fₙ F hFn hinj hF hne hconv Q hQ hQH R hR hQR J hJ E D hE hD hnull hretain
    v hv hlim η (fun _ => σ) τ Rₙ hregion G q hq hG hwindow

end SLEExactGauge.RetainedTubeSausage

end

end OAI
