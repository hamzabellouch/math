import OAI.Probability.FreeIsing.Posterior.StoppingTimes

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PosteriorCompensatorStopping

open PosteriorStoppingTimes

def jointExit {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    WithTop ℝ≥0 :=
  min (posteriorExit M n ω) (rationalExit A ((n : ℝ) + 1) ω)

theorem jointExit_le_posteriorExit {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (ω : Ω) : jointExit M A n ω ≤ posteriorExit M n ω := min_le_left _ _

theorem jointExit_le_cap {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    jointExit M A n ω ≤ (((n : ℝ≥0) + 1) : WithTop ℝ≥0) :=
  (jointExit_le_posteriorExit M A n ω).trans (posteriorExit_le_cap M n ω)

theorem jointExit_ne_top {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    jointExit M A n ω ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (jointExit_le_cap M A n ω)

theorem jointExit_mono {Ω : Type*} (M A : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Monotone (fun n => jointExit M A n ω) := by
  intro n m hnm
  exact min_le_min (posteriorExit_mono M ω hnm)
    (rationalExit_mono A ω (by exact_mod_cast Nat.add_le_add_right hnm 1))

theorem isStoppingTime_jointExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous] {M A : ℝ≥0 → Ω → ℝ}
    (hM : Adapted F M) (hA : Adapted F A) (n : ℕ) :
    IsStoppingTime F (jointExit M A n) :=
  (isStoppingTime_posteriorExit hM n).min (isStoppingTime_rationalExit hA _)

theorem abs_stoppedProcess_le_of_le_exit {Ω : Type*} {X : ℝ≥0 → Ω → ℝ}
    {τ : Ω → WithTop ℝ≥0} {ω : Ω} {r : ℝ}
    (hc : Continuous (fun t => X t ω)) (hzero : |X 0 ω| ≤ r)
    (hτ : τ ω ≤ rationalExit X r ω) (t : ℝ≥0) :
    |stoppedProcess X τ t ω| ≤ r := by
  let s : WithTop ℝ≥0 := min (t : WithTop ℝ≥0) (τ ω)
  have hsne : s ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hsne
  have huτ : (u : WithTop ℝ≥0) ≤ rationalExit X r ω := by
    rw [hu]
    exact (min_le_right _ _).trans hτ
  change |X s.untopA ω| ≤ r
  rw [← hu]
  exact abs_le_of_le_rationalExit hc hzero huτ

theorem abs_stopped_posterior_le {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => M t ω)) (hzero : M 0 ω = 0) (n : ℕ) (t : ℝ≥0) :
    |stoppedProcess M (jointExit M A n) t ω| ≤ threshold n := by
  apply abs_stoppedProcess_le_of_le_exit hc
    (by simpa only [hzero, abs_zero] using threshold_nonneg n) _ t
  exact (jointExit_le_posteriorExit M A n ω).trans (min_le_left _ _)

theorem abs_stopped_compensator_le {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => A t ω)) (hzero : A 0 ω = 0) (n : ℕ) (t : ℝ≥0) :
    |stoppedProcess A (jointExit M A n) t ω| ≤ (n : ℝ) + 1 := by
  apply abs_stoppedProcess_le_of_le_exit hc
    (by simp only [hzero, abs_zero]; positivity) (min_le_right _ _) t

theorem eventually_le_compensatorExit {Ω : Type*} {A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun t => A t ω)) (T : ℝ≥0) :
    ∀ᶠ n : ℕ in atTop, (T : WithTop ℝ≥0) ≤ rationalExit A ((n : ℝ) + 1) ω := by
  obtain ⟨r, hr⟩ := isCompact_Icc.bddAbove_image
    (hc.abs.continuousOn : ContinuousOn (fun t => |A t ω|) (Icc 0 T))
  have hn : ∀ᶠ n : ℕ in atTop, r ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop r)
  filter_upwards [hn] with n hnr
  apply le_rationalExit_of_bound
  intro t ht
  exact (hr (mem_image_of_mem _ ⟨zero_le, ht⟩)).trans (by linarith)

theorem eventually_le_jointExit {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {T : ℝ≥0} (hM : ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hA : Continuous (fun t => A t ω)) :
    ∀ᶠ n in atTop, (T : WithTop ℝ≥0) ≤ jointExit M A n ω := by
  filter_upwards [eventually_le_posteriorExit hM, eventually_le_compensatorExit hA T]
    with n hn hA
  exact le_min hn hA

theorem tendsto_jointExit_top {Ω : Type*} {M A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hM : ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hA : Continuous (fun t => A t ω)) :
    Tendsto (fun n => jointExit M A n ω) atTop (𝓝 ⊤) := by
  apply (WithTop.tendsto_nhds_top_iff _).2
  intro T
  filter_upwards [eventually_le_jointExit (hM (T + 1)) hA] with n hn
  exact (WithTop.coe_lt_coe.mpr (lt_add_one T)).trans_le hn

theorem isLocalizingSequence_jointExit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {F : Filtration ℝ≥0 mΩ} [F.IsRightContinuous]
    {M A : ℝ≥0 → Ω → ℝ} (hM : Adapted F M) (hA : Adapted F A)
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω)) :
    IsLocalizingSequence F (jointExit M A) μ where
  isStoppingTime := isStoppingTime_jointExit hM hA
  tendsto_top := by
    filter_upwards [hcompact, hcA] with ω hm ha using tendsto_jointExit_top hm ha
  mono := ae_of_all _ (jointExit_mono M A)

theorem isLocalizingSequence_jointExit_rightCont {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}
    (hM : Adapted F M) (hA : Adapted F A)
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω)) :
    IsLocalizingSequence F.rightCont (jointExit M A) μ := by
  apply isLocalizingSequence_jointExit _ _ hcompact hcA
  · exact fun t => (hM t).mono (F.le_rightCont t) le_rfl
  · exact fun t => (hA t).mono (F.le_rightCont t) le_rfl

theorem eventually_stoppedProcess_eq_on {Ω E : Type*} {M A : ℝ≥0 → Ω → ℝ}
    (X : ℝ≥0 → Ω → E) {ω : Ω} {T : ℝ≥0}
    (hM : ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hA : Continuous (fun t => A t ω)) :
    ∀ᶠ n in atTop, ∀ t ≤ T, stoppedProcess X (jointExit M A n) t ω = X t ω := by
  filter_upwards [eventually_le_jointExit hM hA] with n hn
  intro t ht
  exact stoppedProcess_eq_of_le ((WithTop.coe_le_coe.mpr ht).trans hn)

theorem ae_all_eq_of_stopped_eq {Ω E : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {M A : ℝ≥0 → Ω → ℝ} {X Y : ℝ≥0 → Ω → E}
    (hcompact : ∀ᵐ ω ∂μ, ∀ T : ℝ≥0, ∃ r < (1 : ℝ), ∀ t ≤ T, |M t ω| ≤ r)
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hstop : ∀ n, ∀ᵐ ω ∂μ, ∀ t,
      stoppedProcess X (jointExit M A n) t ω = stoppedProcess Y (jointExit M A n) t ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  have hstop' := ae_all_iff.mpr hstop
  filter_upwards [hcompact, hcA, hstop'] with ω hm ha hs
  intro t
  obtain ⟨n, hn⟩ := (eventually_le_jointExit (hm t) ha).exists
  rw [← stoppedProcess_eq_of_le (u := X) hn, ← stoppedProcess_eq_of_le (u := Y) hn]
  exact hs n t

end Problem367.PosteriorCompensatorStopping

end

end OAI
