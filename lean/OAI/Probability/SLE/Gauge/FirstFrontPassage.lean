import OAI.Probability.SLE.Gauge.RetainedTubeSausage

namespace OAI

/-! The retained endpoint and pre-front margins give an actual first-front
stopping time, with the retained middle interval strictly before it. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.FirstFrontPassage
open PassageRetention RetainedTubeSausage

/-- First time a scalar progress coordinate reaches the front. -/
def firstFrontTime (x : ℝ≥0 → ℝ) (q : ℝ) : WithTop ℝ≥0 :=
  hittingAfter (fun t (_ : Unit) => x t - q) {0} 0 ()

/-- Finite-valued representative; it agrees with the actual first-front
hitting time whenever a retained endpoint witnesses a crossing. -/
def frontTime (x : ℝ≥0 → ℝ) (q : ℝ) : ℝ≥0 :=
  (firstFrontTime x q).untopD 0

theorem firstFrontTime_isStoppingTime
    {Ω : Type*} [m : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 m)
    (x : ℝ≥0 → Ω → ℝ) (ha : Adapted ℱ x)
    (hc : ∀ ω, Continuous (fun t => x t ω)) (q : ℝ) :
    IsStoppingTime ℱ (fun ω => firstFrontTime (fun t => x t ω) q) := by
  exact continuous_zero_hit_stopping ℱ (fun t ω => x t ω - q)
    (fun t => (ha t).sub_const q) (fun ω => (hc ω).sub continuous_const) 0

/-- A continuous crossing before a finite endpoint makes the infimum defining
the stopping time an actual least crossing, even without global continuity. -/
theorem exists_first_front
    (x : ℝ≥0 → ℝ) (q : ℝ) (T : ℝ≥0)
    (hc : ContinuousOn x (Icc 0 T)) (hstart : x 0 < q) (hend : q < x T) :
    ∃ τ : ℝ≥0, firstFrontTime x q = (τ : WithTop ℝ≥0) ∧
      0 < τ ∧ τ < T ∧ x τ = q ∧ ∀ t < τ, x t < q := by
  let K := Icc (0 : ℝ≥0) T ∩ x ⁻¹' {q}
  have hKc : IsClosed K := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hKc inter_subset_left
  have hKn : K.Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ T from bot_le)
      hc ⟨hstart.le, hend.le⟩
    exact ⟨t, ht, he⟩
  obtain ⟨τ, hτ, hmin⟩ := hK.exists_isLeast hKn
  have hhit : x τ = q := hτ.2
  have hpos : 0 < τ := lt_of_le_of_ne bot_le (by
    intro he
    exact (ne_of_lt hstart) (he ▸ hhit))
  have hlt : τ < T := lt_of_le_of_ne hτ.1.2 (by
    intro he
    exact (ne_of_gt hend) (he ▸ hhit))
  have hprior (t : ℝ≥0) (ht : t < τ) : x t < q := by
    by_contra hn
    obtain ⟨u, hu, hue⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from bot_le)
      (hc.mono (Icc_subset_Icc_right (ht.le.trans hτ.1.2)))
      ⟨hstart.le, le_of_not_gt hn⟩
    exact (not_le_of_gt ht) ((hmin ⟨⟨bot_le, hu.2.trans (ht.le.trans hτ.1.2)⟩, hue⟩).trans hu.2)
  have hleast : IsLeast {t : ℝ≥0 | 0 ≤ t ∧ x t - q ∈ ({0} : Set ℝ)} τ := by
    refine ⟨⟨bot_le, by simp only [mem_singleton_iff, hhit, sub_self]⟩, ?_⟩
    intro t ht
    by_contra hn
    exact (ne_of_lt (hprior t (lt_of_not_ge hn))) (sub_eq_zero.mp ht.2)
  have htime : firstFrontTime x q = (τ : WithTop ℝ≥0) := by
    unfold firstFrontTime hittingAfter
    rw [ite_eq_left ⟨τ, hleast.1⟩, hleast.csInf_eq]
  exact ⟨τ, htime, hpos, hlt, hhit, hprior⟩

/-- Early containment and a retained pre-front prefix force the actual first
front stop to fall strictly after the retained middle interval. -/
theorem frontTime_between
    (x : ℝ≥0 → ℝ) (q : ℝ) (σ b T : ℝ≥0) (_hσb : σ ≤ b) (_hbT : b < T)
    (hc : ContinuousOn x (Icc 0 T))
    (hearly : ∀ t ∈ Icc 0 σ, x t < q)
    (hprefix : ∀ t ∈ Icc σ b, x t < q) (hend : q < x T) :
    firstFrontTime x q = (frontTime x q : WithTop ℝ≥0) ∧
      b < frontTime x q ∧ frontTime x q < T ∧ x (frontTime x q) = q := by
  obtain ⟨τ, hτ, _, hτT, hhit, _⟩ := exists_first_front x q T hc
    (hearly 0 ⟨le_rfl, bot_le⟩) hend
  have hbτ : b < τ := by
    by_contra hn
    have hτb : τ ≤ b := le_of_not_gt hn
    have hlt : x τ < q := by
      by_cases hτσ : τ ≤ σ
      · exact hearly τ ⟨bot_le, hτσ⟩
      · exact hprefix τ ⟨le_of_not_ge hτσ, hτb⟩
    exact (ne_of_lt hlt) hhit
  have hfront : frontTime x q = τ := by simp only [frontTime, hτ, WithTop.untopD_coe]
  exact ⟨hfront ▸ hτ, hfront ▸ hbτ, hfront ▸ hτT, hfront ▸ hhit⟩

/-- Lower endpoint margins transfer by the same compact uniform-convergence
argument as upper pre-front margins. -/
theorem eventually_front_lt_on_compact_image
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hF : ContinuousOn F upperHalfPlane)
    (hFconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (pₙ : ℕ → ℂ → ℝ) (p : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hp : ContinuousOn p U) (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (hKU : F '' K ⊆ U) (q : ℝ) (hbound : ∀ z ∈ K, q < p (F z)) :
    ∀ᶠ n in atTop, ∀ z ∈ K, q < pₙ n (Fₙ n z) := by
  have hnegconv : TendstoLocallyUniformlyOn (fun n z => -pₙ n z) (fun z => -p z) atTop U :=
    hpconv.neg
  have hh := eventually_front_lt_on_compact Fₙ F hF hFconv
    (fun n z => -pₙ n z) (fun z => -p z) U hU hp.neg hnegconv K hK hKH hKU (-q)
    (fun z hz => neg_lt_neg (hbound z hz))
  filter_upwards [hh] with n hn z hz
  exact neg_lt_neg_iff.mp (hn z hz)

/-- Retained endpoint margins construct the actual finite first-front stop.
The positive stopped sausage bound therefore needs no assumed front-stop fact. -/
theorem retained_tube_firstFront_sausage_mass
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
    (hp : ContinuousOn p U) (hpn : ∀ n, ContinuousOn (pₙ n) U)
    (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (hFOU : MapsTo F O U) (hW : W ⊆ {z | 1 < p (F z)})
    (E : Set Ω) (hE : MeasurableSet E)
    (htube : E ⊆ stoppedPhysicalTube (fun ω => f ω) σ O W)
    (hstart : ∀ ω ∈ E, p (F (f ω (σ ω))) < 1 / 3)
    (R : Set ℂ) (hR : IsOpen R)
    (hmiddle : ∀ z ∈ O, 1 / 3 < p (F z) → p (F z) < 2 / 3 → F z ∈ R)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ᶠ n in atTop, R ⊆ Rₙ n)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n ∩ E))
    (hη : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω ≤ t → f ω t ∈ upperHalfPlane →
      η n ω t = Fₙ n (f ω t))
    (hηc : ∀ n, ∀ᵐ ω ∂P, Continuous (η n ω))
    (hearly : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E →
      MapsTo (η n ω) (Icc 0 (σ ω)) U ∧
        ∀ t ∈ Icc 0 (σ ω), pₙ n (η n ω t) < 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 4) ≤ P {ω | ω ∈ G n ∩ E ∧ ENNReal.ofReal a ≤
        segmentSausageCharge κ (η n ω) (σ ω) (frontTime (fun t => pₙ n (η n ω t)) 1) (v n) (Rₙ n)} := by
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
      σ ω ≤ (J i).1 ∧ (J i).2 ≤ frontTime (fun t => pₙ n (η n ω t)) 1 ∧
        EqOn (η n ω) (fun u => Fₙ n (f ω u)) (Icc (J i).1 (J i).2) := by
    intro i
    let j := enumerateRetainedPassage i
    have hLH : L j.1.2.2.2 ⊆ upperHalfPlane := fun z hz => hOH ((hL _).2 hz).1
    have hLU : F '' L j.1.2.2.2 ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFOU ((hL _).2 hz).1
    have hlt := eventually_front_lt_on_compact Fₙ F hF.continuousOn hconv pₙ p U hU hp hpconv
      (L j.1.2.2.2) (hL _).1 hLH hLU (2 / 3) (fun z hz => ((hL _).2 hz).2)
    have hKH : K j.1.2.1 ⊆ upperHalfPlane := fun z hz => hOH ((hK _).2 hz)
    have hKU : F '' K j.1.2.1 ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFOU ((hK _).2 hz)
    have himage := eventually_image_compact_subset_open Fₙ F hconv hF.continuousOn
      (K j.1.2.1) (hK _).1 hKH U hU hKU
    have hNH : N j.2 ⊆ upperHalfPlane := fun z hz => hOH ((hN _).2 hz).1
    have hNU : F '' N j.2 ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFOU ((hN _).2 hz).1
    have hgt := eventually_front_lt_on_compact_image Fₙ F hF.continuousOn hconv pₙ p U hU
      hp hpconv (N j.2) (hN _).1 hNH hNU 1 (fun z hz => ((hN _).2 hz).2)
    filter_upwards [hlt, hgt, himage, hearly] with n hnL hnN hnK hearlyn
    filter_upwards [hη n, hηc n, hearlyn] with ω hηω hηcω hearlyω
    intro hω
    have hDi : ω ∈ retainedPassageCertificate f σ K M L N
        (beyondFrontRegion O progress) j := hω.2
    obtain ⟨⟨hσs, _, hfull, hmid, hlow⟩, hend⟩ := hDi
    obtain ⟨hearlyU, hearlylt⟩ := hearlyω hω.1
    have hpathU : MapsTo (η n ω) (Icc 0 (passageEnd j.1)) U := by
      intro t ht
      by_cases hts : t ≤ σ ω
      · exact hearlyU ⟨bot_le, hts⟩
      · have hst : σ ω ≤ t := (lt_of_not_ge hts).le
        have hmem := hfull.2 ⟨hst, ht.2⟩
        rw [hηω t hst (hKH hmem)]
        exact hnK (mem_image_of_mem (Fₙ n) hmem)
    have hc : ContinuousOn (fun t => pₙ n (η n ω t)) (Icc 0 (passageEnd j.1)) :=
      (hpn n).comp hηcω.continuousOn hpathU
    have hprefix : ∀ t ∈ Icc (σ ω) (intervalEnd j.1), pₙ n (η n ω t) < 1 := by
      intro t ht
      have hmem := hlow.2 ht
      rw [hηω t ht.1 (hLH hmem)]
      exact (hnL _ hmem).trans (by norm_num)
    have hendgt : 1 < pₙ n (η n ω (passageEnd j.1)) := by
      have hmem := hfull.2 ⟨hfull.1, le_rfl⟩
      rw [hηω _ hfull.1 (hKH hmem)]
      exact hnN _ hend
    have hfront := frontTime_between (fun t => pₙ n (η n ω t)) 1
      (σ ω) (intervalEnd j.1) (passageEnd j.1)
      (hσs.le.trans (intervalStart_lt_end _).le) (intervalEnd_lt_passageEnd _)
      hc hearlylt hprefix hendgt
    refine ⟨hσs.le, hfront.2.1.le, ?_⟩
    intro t ht
    exact hηω t (hσs.le.trans ht.1) (hOH ((hM _).2 (hmid ht)).1)
  exact countable_stopped_mass_ae_window_eventually P κ hκ hκ8 (fun ω => f ω) hSLE
    Fₙ F hFn hinj hF hne hconv Q hQ hQH R hR hQR J hJ E D hE hD hnull hretain
    v hv hlim η (fun _ => σ) (fun n ω => frontTime (fun t => pₙ n (η n ω t)) 1)
    Rₙ hregion G q hq hG hwindow


end SLEExactGauge.FirstFrontPassage

end

end OAI
