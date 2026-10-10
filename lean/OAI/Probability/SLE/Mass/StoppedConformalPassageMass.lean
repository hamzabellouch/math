import OAI.Probability.SLE.Mass.CompactConformalPassageMass

namespace OAI

/-! Retained sausage mass before the actual passage stop. The physical
curve may include boundary visits; only its retained interior interval is
identified with the conformal image. All mass is charged to the prescribed
stopped segment, rather than to later portions of the whole trace. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

def segmentSausageCharge (κ : ℝ) (η : ℝ≥0 → ℂ) (s t : ℝ≥0)
    (v : ℝ) (R : Set ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (v ^ (-codimension κ)) * volume (R ∩ sourceSausageSet η s t v)

theorem sourceSausageSet_mono_interval
    (η : ℝ≥0 → ℂ) {s t a b : ℝ≥0} (hsa : s ≤ a) (hbt : b ≤ t) (v : ℝ) :
    sourceSausageSet η a b v ⊆ sourceSausageSet η s t v := by
  rintro z ⟨u, hu, hd⟩
  exact ⟨u, ⟨hsa.trans hu.1, hu.2.trans hbt⟩, hd⟩

theorem sourceSausageSet_congr_interval
    {η ξ : ℝ≥0 → ℂ} {s t : ℝ≥0} (heq : EqOn η ξ (Icc s t)) (v : ℝ) :
    sourceSausageSet η s t v = sourceSausageSet ξ s t v := by
  ext z
  constructor <;> rintro ⟨u, hu, hd⟩
  · exact ⟨u, hu, by simpa only [heq hu] using hd⟩
  · exact ⟨u, hu, by simpa only [heq hu] using hd⟩

theorem segmentSausageCharge_mono
    (κ : ℝ) (η : ℝ≥0 → ℂ) {s t a b : ℝ≥0}
    (hsa : s ≤ a) (hbt : b ≤ t) (v : ℝ) {R S : Set ℂ} (hRS : R ⊆ S) :
    segmentSausageCharge κ η a b v R ≤ segmentSausageCharge κ η s t v S :=
  mul_le_mul' le_rfl (measure_mono (inter_subset_inter hRS
    (sourceSausageSet_mono_interval η hsa hbt v)))

/-- The finite-list conformal transfer charges only the actual stopped
physical passage. Its values at parameter-boundary times can be supplied by
the boundary-safe restart theorem. -/
theorem compact_conformal_stopped_passage_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : Set ℂ) (hK : IsCompact K) (hKn : K.Nonempty) (hKH : K ⊆ upperHalfPlane)
    (R : Set ℂ) (hR : IsOpen R) (himage : F '' K ⊆ R)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : ∀ J ∈ I, J.1 < J.2)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (s t : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n))
    (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
    (hretain : ∀ᶠ n in atTop, ∀ ω, ω ∈ G n →
      ∃ J ∈ I, γ ω '' Icc J.1 J.2 ⊆ K ∧ s n ω ≤ J.1 ∧ J.2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc J.1 J.2)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 2) ≤ P {ω | ω ∈ G n ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (s n ω) (t n ω) (v n) (Rₙ n)} := by
  obtain ⟨c, ell, v₀, hc, hell, hv₀, htransfer⟩ := eventually_compact_sausage_transfer
    κ Fₙ F hFn hinj hF hne hconv K hK hKn hKH R hR himage
  have hcoeff : 0 < c ^ 2 * ell ^ codimension κ :=
    mul_pos (sq_pos_of_pos hc) (Real.rpow_pos_of_pos hell _)
  have hsmall : ∀ᶠ n in atTop, v n < v₀ := hlim.eventually (gt_mem_nhds hv₀)
  have hlim' : Tendsto (fun n => ell * v n) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  have htrans : ∀ᶠ n in atTop, ∀ ω, ω ∈ G n → True ∧
      ∃ J ∈ I, ENNReal.ofReal (c ^ 2 * ell ^ codimension κ) *
        sourceSausageMass κ (γ ω) J.1 J.2 (ell * v n) ≤
        segmentSausageCharge κ (η n ω) (s n ω) (t n ω) (v n) (Rₙ n) := by
    filter_upwards [htransfer, hretain, hsmall, hregion] with n hn hr hs hRsub
    intro ω hω
    obtain ⟨J, hJI, hJK, hJs, hJt, heq⟩ := hr ω hω
    refine ⟨trivial, J, hJI, (hn (γ ω) J.1 J.2 hJK (v n) (hv n) hs).trans ?_⟩
    change segmentSausageCharge κ (fun u => Fₙ n (γ ω u)) J.1 J.2 (v n) R ≤ _
    have hsausage := sourceSausageSet_congr_interval heq (v n)
    unfold segmentSausageCharge
    rw [← hsausage]
    exact segmentSausageCharge_mono κ (η n ω) hJs hJt (v n) hRsub
  obtain ⟨a, ha, hmass⟩ := ribbon_passage_mass_of_eventually_finite_intervals
    P κ hκ hκ8 γ hSLE I hI (fun n => ell * v n)
    (fun n => mul_pos hell (hv n)) hlim' G q hq hG
    (fun n ω => segmentSausageCharge κ (η n ω) (s n ω) (t n ω) (v n) (Rₙ n))
    (fun _ _ => True) (c ^ 2 * ell ^ codimension κ) hcoeff htrans
  exact ⟨a, ha, by simpa only [true_and] using hmass⟩

/-- Almost-sure chart identities suffice; exceptional restart paths are
removed without changing the probabilities of the retained events. -/
theorem compact_conformal_stopped_passage_mass_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hFn : ∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane)
    (hinj : ∀ n, InjOn (Fₙ n) upperHalfPlane)
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hne : ∀ z ∈ upperHalfPlane, deriv F z ≠ 0)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (K : Set ℂ) (hK : IsCompact K) (hKn : K.Nonempty) (hKH : K ⊆ upperHalfPlane)
    (R : Set ℂ) (hR : IsOpen R) (himage : F '' K ⊆ R)
    (I : Finset (ℝ≥0 × ℝ≥0)) (hI : ∀ J ∈ I, J.1 < J.2)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (s t : ℕ → Ω → ℝ≥0) (Rₙ : ℕ → Set ℂ)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n))
    (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
    (hretain : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n →
      ∃ J ∈ I, γ ω '' Icc J.1 J.2 ⊆ K ∧ s n ω ≤ J.1 ∧ J.2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc J.1 J.2)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 2) ≤ P {ω | ω ∈ G n ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (s n ω) (t n ω) (v n) (Rₙ n)} := by
  let H (n : ℕ) : Set Ω := {ω | ω ∈ G n ∧
      ∃ J ∈ I, γ ω '' Icc J.1 J.2 ⊆ K ∧ s n ω ≤ J.1 ∧ J.2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc J.1 J.2)}
  have hH : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (H n) := by
    filter_upwards [hG, hretain] with n hn hr
    have he : H n =ᵐ[P] G n := by
      filter_upwards [hr] with ω hω
      exact propext ⟨fun h => h.1, fun h => ⟨h, hω h⟩⟩
    simpa only [measure_congr he] using hn
  have hr : ∀ᶠ n in atTop, ∀ ω, ω ∈ H n →
      ∃ J ∈ I, γ ω '' Icc J.1 J.2 ⊆ K ∧ s n ω ≤ J.1 ∧ J.2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc J.1 J.2) :=
    Eventually.of_forall fun _ _ hω => hω.2
  obtain ⟨a, ha, hm⟩ := compact_conformal_stopped_passage_mass P κ hκ hκ8 γ hSLE
    Fₙ F hFn hinj hF hne hconv K hK hKn hKH R hR himage I hI v hv hlim
    η s t Rₙ H q hq hH hregion hr
  refine ⟨a, ha, ?_⟩
  filter_upwards [hm] with n hn
  exact hn.trans (measure_mono fun _ hω => ⟨hω.1.1, hω.2⟩)

/-- Countable compact/time certificates are extracted before choosing the
common mesh. The selected intervals lie before the actual passage stop. -/
theorem countable_compact_conformal_stopped_passage_mass
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
    (hwindow : ∀ i, ∀ᶠ n in atTop, ∀ ω, ω ∈ G n ∩ E ∩ D i →
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
  have hwin : ∀ᶠ n in atTop, ∀ i ∈ Finset.range N, ∀ ω, ω ∈ G n ∩ E ∩ D i →
      s n ω ≤ (J i).1 ∧ (J i).2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc (J i).1 (J i).2) :=
    (Finset.eventually_all _).mpr (fun i _ => hwindow i)
  have hr : ∀ᶠ n in atTop, ∀ ω, ω ∈ H n →
      ∃ L ∈ I, γ ω '' Icc L.1 L.2 ⊆ Q ∧ s n ω ≤ L.1 ∧ L.2 ≤ t n ω ∧
        EqOn (η n ω) (fun u => Fₙ n (γ ω u)) (Icc L.1 L.2) := by
    filter_upwards [hwin] with n hn
    intro ω hω
    obtain ⟨i, hi, hDi⟩ := mem_iUnion₂.mp hω.2
    exact ⟨J i, Finset.mem_image.mpr ⟨i, hi, rfl⟩,
      (hretain i ω hDi).trans (subset_iUnion₂_of_subset i hi Subset.rfl),
      hn i hi ω ⟨hω.1, hDi⟩⟩
  obtain ⟨a, ha, hmass⟩ := compact_conformal_stopped_passage_mass P κ hκ hκ8 γ hSLE
    Fₙ F hFn hinj hF hne hconv Q hQ hQn hQH R hR hQR I hI v hv hlim
    η s t Rₙ H (q / 2) (by positivity) (Eventually.of_forall hN) hregion hr
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmass] with n hn
  have hqq : q / 2 / 2 = q / 4 := by ring
  rw [hqq] at hn
  exact hn.trans (measure_mono (fun _ hω => ⟨hω.1.1, hω.2⟩))

end SLEExactGauge

end

end OAI
