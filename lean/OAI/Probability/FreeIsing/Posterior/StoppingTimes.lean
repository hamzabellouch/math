import OAI.Probability.FreeIsing.Posterior.InteriorLocalization

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorStoppingTimes

def rationalExit {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (r : ℝ) (ω : Ω) :
    WithTop ℝ≥0 :=
  ⨅ q : ℚ≥0, if r < |M (q : ℝ≥0) ω| then ((q : ℝ≥0) : WithTop ℝ≥0) else ⊤

theorem isStoppingTime_decision {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {p : Ω → Prop} [DecidablePred p]
    (q : ℝ≥0) (hp : MeasurableSet[F q] {ω | p ω}) :
    IsStoppingTime F (fun ω => if p ω then (q : WithTop ℝ≥0) else ⊤) := by
  intro t
  by_cases hqt : q ≤ t
  · have heq : {ω | (if p ω then (q : WithTop ℝ≥0) else ⊤) ≤ t} = {ω | p ω} := by
      ext ω
      by_cases hpω : p ω
      · simp only [hpω, ite_true, mem_ofPred_eq, iff_true]
        exact WithTop.coe_le_coe.mpr hqt
      · simp only [hpω, ite_false, mem_ofPred_eq, iff_false]
        exact not_le.mpr (WithTop.coe_lt_top t)
    rw [heq]
    exact F.mono hqt _ hp
  · have heq : {ω | (if p ω then (q : WithTop ℝ≥0) else ⊤) ≤ t} = ∅ := by
      ext ω
      by_cases hpω : p ω
      · simp only [hpω, ite_true, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hqt (WithTop.coe_le_coe.mp h)
      · simp only [hpω, ite_false, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact not_le.mpr (WithTop.coe_lt_top t)
    rw [heq]
    exact @MeasurableSet.empty Ω (F t)

theorem isStoppingTime_rationalExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
    {M : ℝ≥0 → Ω → ℝ} (hM : Adapted F M) (r : ℝ) :
    IsStoppingTime F (rationalExit M r) := by
  apply IsStoppingTime.iInf
  intro q
  apply isStoppingTime_decision
  let : MeasurableSpace Ω := F (q : ℝ≥0)
  exact (hM (q : ℝ≥0)).abs measurableSet_Ioi

theorem isStoppingTime_rationalExit_rightCont {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} (hM : Adapted F M) (r : ℝ) :
    IsStoppingTime F.rightCont (rationalExit M r) := by
  apply isStoppingTime_rationalExit
  intro t
  exact (hM t).mono (F.le_rightCont t) le_rfl

theorem rationalExit_mono {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Monotone (fun r => rationalExit M r ω) := by
  intro r s hrs
  apply iInf_mono
  intro q
  by_cases hs : s < |M (q : ℝ≥0) ω|
  · simp only [hs, hrs.trans_lt hs, ite_true, le_refl]
  · simp [hs]

theorem le_rationalExit_of_bound {Ω : Type*} {M : ℝ≥0 → Ω → ℝ}
    {r : ℝ} {T : ℝ≥0} {ω : Ω}
    (hbound : ∀ t ≤ T, |M t ω| ≤ r) :
    (T : WithTop ℝ≥0) ≤ rationalExit M r ω := by
  apply le_iInf
  intro q
  by_cases hq : r < |M (q : ℝ≥0) ω|
  · simp only [hq, ite_true, WithTop.coe_le_coe]
    exact le_of_not_gt (fun h => (not_lt_of_ge (hbound q h.le)) hq)
  · simp only [hq, ite_false]
    exact le_top

theorem exists_earlier_nnrat {f : ℝ≥0 → ℝ} {t : ℝ≥0} {r : ℝ}
    (hc : ContinuousAt f t) (ht : 0 < t) (hr : r < f t) :
    ∃ q : ℚ≥0, (q : ℝ≥0) < t ∧ r < f (q : ℝ≥0) := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hc (f t - r) (sub_pos.mpr hr)
  have htR : (0 : ℝ) < t := ht
  have hlo : max (0 : ℝ) ((t : ℝ) - δ) < t :=
    max_lt htR (sub_lt_self _ hδ)
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hlo
  have hq0 : 0 ≤ q := Rat.cast_nonneg.mp (le_of_lt ((le_max_left _ _).trans_lt hqlo))
  let qn : ℚ≥0 := ⟨q, hq0⟩
  have hqn : ((qn : ℝ≥0) : ℝ) = (q : ℝ) := by
    norm_cast
  have hqt : (qn : ℝ≥0) < t := by exact_mod_cast (hqn ▸ hqhi)
  refine ⟨qn, hqt, ?_⟩
  have hd : dist (qn : ℝ≥0) t < δ := by
    rw [NNReal.dist_eq, hqn, abs_of_neg (sub_neg.mpr hqhi)]
    have := (le_max_right (0 : ℝ) ((t : ℝ) - δ)).trans_lt hqlo
    linarith
  have hsmall := hcont hd
  rw [Real.dist_eq] at hsmall
  have hleft := (abs_lt.mp hsmall).1
  linarith

theorem abs_le_of_le_rationalExit {Ω : Type*} {M : ℝ≥0 → Ω → ℝ}
    {r : ℝ} {ω : Ω} (hc : Continuous (fun t => M t ω))
    (hzero : |M 0 ω| ≤ r) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ rationalExit M r ω) : |M t ω| ≤ r := by
  by_cases ht0 : t = 0
  · simpa [ht0] using hzero
  by_contra hbound
  obtain ⟨q, hqt, hq⟩ := exists_earlier_nnrat hc.abs.continuousAt
    (pos_iff_ne_zero.mpr ht0) (lt_of_not_ge hbound)
  have hexit : rationalExit M r ω ≤ ((q : ℝ≥0) : WithTop ℝ≥0) := by
    exact (iInf_le (fun p : ℚ≥0 => if r < |M (p : ℝ≥0) ω| then
      ((p : ℝ≥0) : WithTop ℝ≥0) else ⊤) q).trans
        (by simp only [hq, ite_true, le_refl])
  have hle : t ≤ (q : ℝ≥0) := WithTop.coe_le_coe.mp (ht.trans hexit)
  exact (not_lt_of_ge hle) hqt

abbrev threshold := PosteriorInteriorLocalization.radius

def posteriorExit {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    WithTop ℝ≥0 :=
  min (rationalExit M (threshold n) ω) (((n : ℝ≥0) + 1) : WithTop ℝ≥0)

theorem threshold_nonneg (n : ℕ) : 0 ≤ threshold n :=
  PosteriorInteriorLocalization.radius_nonneg n

theorem threshold_lt_one (n : ℕ) : threshold n < 1 :=
  PosteriorInteriorLocalization.radius_lt_one n

theorem threshold_mono : Monotone threshold :=
  PosteriorInteriorLocalization.radius_monotone

theorem isStoppingTime_posteriorExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
    {M : ℝ≥0 → Ω → ℝ} (hM : Adapted F M) (n : ℕ) :
    IsStoppingTime F (posteriorExit M n) :=
  (isStoppingTime_rationalExit hM (threshold n)).min_const ((n : ℝ≥0) + 1)

theorem posteriorExit_mono {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Monotone (fun n => posteriorExit M n ω) := by
  intro n m hnm
  apply min_le_min
  · exact rationalExit_mono M ω (threshold_mono hnm)
  · exact_mod_cast (show (n : ℝ≥0) + 1 ≤ (m : ℝ≥0) + 1 by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem posteriorExit_le_cap {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    posteriorExit M n ω ≤ (((n : ℝ≥0) + 1) : WithTop ℝ≥0) := min_le_right _ _

theorem posteriorExit_ne_top {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    posteriorExit M n ω ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (posteriorExit_le_cap M n ω)

theorem abs_stoppedProcess_le {Ω : Type*} {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (hzero : M 0 ω = 0) (n : ℕ) (t : ℝ≥0) :
    |stoppedProcess M (posteriorExit M n) t ω| ≤ threshold n := by
  let s : WithTop ℝ≥0 := min (t : WithTop ℝ≥0) (posteriorExit M n ω)
  have hsne : s ≠ ⊤ := ne_top_of_le_ne_top (show (t : WithTop ℝ≥0) ≠ ⊤ from WithTop.coe_ne_top) (min_le_left _ _)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hsne
  have huexit : (u : WithTop ℝ≥0) ≤ rationalExit M (threshold n) ω := by
    rw [hu]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hbound := abs_le_of_le_rationalExit hc
    (by simpa only [hzero, abs_zero] using threshold_nonneg n) huexit
  change |M s.untopA ω| ≤ threshold n
  rw [← hu]
  exact hbound

theorem eventually_lt_threshold {r : ℝ} (hr : r < 1) :
    ∀ᶠ n in atTop, r < threshold n :=
  PosteriorInteriorLocalization.tendsto_radius.eventually_const_lt hr

theorem eventually_le_posteriorExit {Ω : Type*} {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {T : ℝ≥0} (hcompact : ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ posteriorExit M n ω := by
  obtain ⟨r, hr, hb⟩ := hcompact
  have hcap : ∀ᶠ n : ℕ in atTop, T ≤ (n : ℝ≥0) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop T)
  filter_upwards [eventually_lt_threshold hr, hcap] with n hn hTn
  apply le_min
  · exact le_rationalExit_of_bound (fun t ht => (hb t ht).trans hn.le)
  · exact WithTop.coe_le_coe.mpr (hTn.trans (le_add_of_nonneg_right zero_le))

theorem tendsto_posteriorExit_top {Ω : Type*} {M : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hcompact : ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r) :
    Tendsto (fun n => posteriorExit M n ω) atTop (𝓝 ⊤) := by
  apply (WithTop.tendsto_nhds_top_iff _).2
  intro T
  filter_upwards [eventually_le_posteriorExit (hcompact (T + 1))] with n hn
  exact (WithTop.coe_lt_coe.mpr (lt_add_one T)).trans_le hn

theorem isLocalizingSequence_posteriorExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
    {M : ℝ≥0 → Ω → ℝ} (hM : Adapted F M)
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r) :
    IsLocalizingSequence F (posteriorExit M) μ where
  isStoppingTime := isStoppingTime_posteriorExit hM
  tendsto_top := hcompact.mono (fun _ h => tendsto_posteriorExit_top h)
  mono := ae_of_all _ (posteriorExit_mono M)

theorem eventually_stoppedProcess_eq_on {Ω E : Type*} {M : ℝ≥0 → Ω → ℝ}
    (X : ℝ≥0 → Ω → E) {ω : Ω} {T : ℝ≥0}
    (hcompact : ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r) :
    ∀ᶠ n in atTop, ∀ t ≤ T, stoppedProcess X (posteriorExit M n) t ω = X t ω := by
  filter_upwards [eventually_le_posteriorExit hcompact] with n hn
  intro t ht
  exact stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr ht).trans hn)

theorem ae_all_eq_of_stopped_eq {Ω E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M : ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → E}
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hstop : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      stoppedProcess X (posteriorExit M n) t ω =
        stoppedProcess Y (posteriorExit M n) t ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  have hstop' := ae_all_iff.mpr hstop
  filter_upwards [hcompact, hstop'] with ω hω hs
  intro t
  obtain ⟨n, hn⟩ := (eventually_le_posteriorExit (hω t)).exists
  rw [← stoppedProcess_eq_of_le (u := X) hn,
    ← stoppedProcess_eq_of_le (u := Y) hn]
  exact hs n t

theorem ae_all_add_eq_of_stopped_add_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M X Y Z : ℝ≥0 → Ω → ℝ}
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hstop : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      stoppedProcess X (posteriorExit M n) t ω =
        stoppedProcess Y (posteriorExit M n) t ω +
          stoppedProcess Z (posteriorExit M n) t ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω + Z t ω := by
  exact ae_all_eq_of_stopped_eq hcompact hstop

theorem isLocalizingSequence_posteriorExit_rightCont {Ω : Type*}
    [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    {M : ℝ≥0 → Ω → ℝ} (hM : Adapted F M)
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r) :
    IsLocalizingSequence F.rightCont (posteriorExit M) μ := by
  apply isLocalizingSequence_posteriorExit _ hcompact
  intro t
  exact (hM t).mono (F.le_rightCont t) le_rfl

theorem isLocalizingSequence_of_field_bound {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {F : Filtration ℝ≥0 mΩ} {M X : ℝ≥0 → Ω → ℝ} {K : ℝ}
    (hM : Adapted F M)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcX : ∀ᵐ ω ∂μ, Continuous (fun t => X t ω))
    (hb : ∀ t, ∀ᵐ ω ∂μ,
      M t ω ∈ Ioo (-1 : ℝ) 1 ∧ |Real.artanh (M t ω) - X t ω| ≤ K) :
    IsLocalizingSequence F.rightCont (posteriorExit M) μ := by
  apply isLocalizingSequence_posteriorExit_rightCont hM
  filter_upwards [PosteriorInteriorLocalization.ae_compact_localization_of_field_bound
    hcM hcX hb] with ω hω
  intro T
  obtain ⟨n, hn⟩ := (hω T).exists
  exact ⟨threshold n, threshold_lt_one n, fun t ht => (hn t ht).le⟩

end Problem367.PosteriorStoppingTimes

end

end OAI
