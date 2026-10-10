import OAI.Probability.SLE.Gauge.PassageSuccess
import OAI.Probability.SLE.Gauge.RetainedRegionMargins

namespace OAI

/-! The actual front-success theorem with moving middle regions. The
physical neighborhoods are selected only after finitely many compact
middle certificates have been retained. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.PassageSuccess
open PassageRetention RetainedTubeSausage FirstFrontPassage

/-- Full front success and mass in the moving middle strip. Local uniform
coordinate convergence supplies its margin on every retained compact;
there is no inclusion assumption on the whole limiting open strip. -/
theorem retained_tube_firstFront_success_mass_middle_regions
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
    (hp : ContinuousOn p U) (hpn : ∀ᶠ n in atTop, ContinuousOn (pₙ n) U)
    (hpconv : TendstoLocallyUniformlyOn pₙ p atTop U)
    (hFOU : MapsTo F O U) (hW : W ⊆ {z | 1 < p (F z)})
    (E : Set Ω) (hE : MeasurableSet E)
    (htube : E ⊆ stoppedPhysicalTube (fun ω => f ω) σ O W)
    (hstart : ∀ ω ∈ E, p (F (f ω (σ ω))) < 1 / 3)
    (V : Set ℂ) (hV : IsOpen V) (hFV : MapsTo F O V)
    (Vₙ : ℕ → Set ℂ) (hVVₙ : ∀ᶠ n in atTop, V ⊆ Vₙ n)
    (aₙ : ℕ → ℂ) (ε : ℝ)
    (hterminal : ∀ n z, z ∈ Vₙ n → pₙ n z = 1 → ‖z - aₙ n‖ < ε / 4)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0))
    (η : ℕ → Ω → ℝ≥0 → ℂ) (Rₙ : ℕ → Set ℂ)
    (hregion : ∀ᶠ n in atTop, U ∩ {z | (1 / 3 : ℝ) < pₙ n z ∧ pₙ n z < 2 / 3} ⊆ Rₙ n)
    (G : ℕ → Set Ω) (q : ℝ) (hq : 0 < q)
    (hG : ∀ᶠ n in atTop, ENNReal.ofReal q ≤ P (G n ∩ E))
    (hη : ∀ n, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω ≤ t → f ω t ∈ upperHalfPlane →
      η n ω t = Fₙ n (f ω t))
    (hηc : ∀ n, ∀ᵐ ω ∂P, Continuous (η n ω))
    (hearly : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E →
      MapsTo (η n ω) (Icc 0 (σ ω)) U ∧
        ∀ t ∈ Icc 0 (σ ω), pₙ n (η n ω t) < 1)
    (hearlyV : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E →
      MapsTo (η n ω) (Icc 0 (σ ω)) (Vₙ n)) :
    ∃ a : ℝ, 0 < a ∧ ∀ᶠ n in atTop,
      ENNReal.ofReal (q / 8) ≤ P {ω |
        ω ∈ FrontSuccess η pₙ σ Vₙ aₙ ε n ∧ ENNReal.ofReal a ≤
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
  have hQR : ∀ i, F '' Q i ⊆ U ∩ {z | (1 / 3 : ℝ) < p z ∧ p z < 2 / 3} := by
    rintro i _ ⟨z, hz, rfl⟩
    have hh := (hM _).2 hz
    exact ⟨hFOU hh.1, hh.2⟩
  have hJ : ∀ i, (J i).1 < (J i).2 := fun i => intervalStart_lt_end _
  have hD : ∀ i, MeasurableSet (D i) := fun i => hDm _
  have hnull : P (E \ ⋃ i, D i) = 0 := by
    rw [sdiff_eq_empty.mpr (nat_retained_cover f σ K M L N _ E hcover), measure_empty]
  have hretain : ∀ i ω, ω ∈ D i →
      (fun t => f ω t) '' Icc (J i).1 (J i).2 ⊆ Q i := by
    intro i ω hω
    exact hω.1.2.2.2.1.image_subset
  let S := FrontSuccess η pₙ σ Vₙ aₙ ε
  have hwindow : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ G n ∩ E ∩ D i →
      (σ ω ≤ (J i).1 ∧ (J i).2 ≤ frontTime (fun t => pₙ n (η n ω t)) 1 ∧
        EqOn (η n ω) (fun u => Fₙ n (f ω u)) (Icc (J i).1 (J i).2)) ∧ ω ∈ S n := by
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
    have hKV : F '' K j.1.2.1 ⊆ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFV ((hK _).2 hz)
    have himageV := eventually_image_compact_subset_open Fₙ F hconv hF.continuousOn
      (K j.1.2.1) (hK _).1 hKH V hV hKV
    have hNH : N j.2 ⊆ upperHalfPlane := fun z hz => hOH ((hN _).2 hz).1
    have hNU : F '' N j.2 ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hFOU ((hN _).2 hz).1
    have hgt := eventually_front_lt_on_compact_image Fₙ F hF.continuousOn hconv pₙ p U hU
      hp hpconv (N j.2) (hN _).1 hNH hNU 1 (fun z hz => ((hN _).2 hz).2)
    filter_upwards [hlt, hgt, himage, himageV, hVVₙ, hearly, hearlyV, hpn] with
      n hnL hnN hnK hnKV hnV hearlyn hearlyVn hpnn
    filter_upwards [hη n, hηc n, hearlyn, hearlyVn] with ω hηω hηcω hearlyω hearlyVω
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
      hpnn.comp hηcω.continuousOn hpathU
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
    refine ⟨⟨hσs.le, hfront.2.1.le, ?_⟩, ?_⟩
    · intro t ht
      exact hηω t (hσs.le.trans ht.1) (hOH ((hM _).2 (hmid ht)).1)
    · have hpathV : MapsTo (η n ω)
          (Icc 0 (frontTime (fun t => pₙ n (η n ω t)) 1)) (Vₙ n) := by
        intro t ht
        by_cases hts : t ≤ σ ω
        · exact hearlyVω hω.1 ⟨bot_le, hts⟩
        · have hst : σ ω ≤ t := (lt_of_not_ge hts).le
          have hmem := hfull.2 ⟨hst, ht.2.trans hfront.2.2.1.le⟩
          rw [hηω t hst (hKH hmem)]
          exact hnV (hnKV (mem_image_of_mem (Fₙ n) hmem))
      exact ⟨hfront.1, hfront.2.2.2,
        hσs.le.trans_lt ((intervalStart_lt_end _).trans hfront.2.1), hpathV, hterminal n _ (hpathV ⟨bot_le, le_rfl⟩) hfront.2.2.2⟩
  have hsuccess : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P,
      ω ∈ G n ∩ E ∩ D i → ω ∈ S n := by
    intro i
    filter_upwards [hwindow i] with n hn
    filter_upwards [hn] with ω hω
    exact fun hw => (hω hw).2
  have hprob := eventual_retained_success_probability P E D G S hE hD hnull q hq hG hsuccess
  have hwin : ∀ i, ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ω ∈ (G n ∩ S n) ∩ E ∩ D i →
      σ ω ≤ (J i).1 ∧ (J i).2 ≤ frontTime (fun t => pₙ n (η n ω t)) 1 ∧
        EqOn (η n ω) (fun u => Fₙ n (f ω u)) (Icc (J i).1 (J i).2) := by
    intro i
    filter_upwards [hwindow i] with n hn
    filter_upwards [hn] with ω hω
    exact fun hw => (hω ⟨⟨hw.1.1.1, hw.1.2⟩, hw.2⟩).1
  obtain ⟨a, ha, hmass⟩ := countable_stopped_mass_ae_window_middle_regions P κ hκ hκ8
    (fun ω => f ω) hSLE Fₙ F hFn hinj hF hne hconv Q hQ hQH pₙ p U hU hp hpconv hQR J hJ E D
    hE hD hnull hretain v hv hlim η (fun _ => σ)
    (fun n ω => frontTime (fun t => pₙ n (η n ω t)) 1)
    Rₙ hregion (fun n => G n ∩ S n) (q / 2) (by positivity) hprob hwin
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmass] with n hn
  have heq : q / 2 / 4 = q / 8 := by ring
  rw [heq] at hn
  exact hn.trans (measure_mono (fun _ hω => ⟨hω.1.1.2, hω.2⟩))


end SLEExactGauge.PassageSuccess

end

end OAI
