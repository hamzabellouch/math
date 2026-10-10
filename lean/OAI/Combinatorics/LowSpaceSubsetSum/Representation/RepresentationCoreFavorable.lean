import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleLedger

namespace OAI

/-! # Favorable probability for the complete representation core ledger

The event includes task initialization, every reported pair, copied replay
state and loop control, in addition to the streamed queries and separator
scans. It is defined on the input-only run and original target.
-/

noncomputable section

namespace LowSpaceSubsetSum

namespace RepresentationData

variable {n : ℕ} (D : RepresentationData n)

def sampledCoreUnits (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : ℕ :=
  (D.scheduleData h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos).coreUnits B (SeparatorCheck.sampledFamilies h.2)

def CoreFavorable (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : Prop :=
  D.sampledTrial hn hlog B h = true ∧
    (D.sampledCoreUnits hn hlog B h : ℝ) ≤
      (inputScale D.input : ℝ) ^ 410 * (2 : ℝ) ^ ((n + 1) / 2)

end RepresentationData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem runtime_core_favorable_of_favorable (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega))
    (hh : R.FavorableTrial hn hlog B h) :
    R.runtimeData.CoreFavorable (by omega) hlog B
      (R.runtimeBucketEquiv (by omega) h) := by
  refine ⟨(R.runtime_sampledTrial_accepts (by omega) hlog B h).mpr hh.1, ?_⟩
  change ((R.runtimeData.scheduleData (R.runtimeHistory h.1.1.1) h.1.1.2
    (by omega) hlog h.1.2.val (primeRange_prime h.1.2.property).pos).coreUnits B
      (SeparatorCheck.sampledFamilies h.2) : ℝ) ≤ _
  rw [R.runtime_schedule_eq]
  apply R.schedule_coreUnits_half h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos B (SeparatorCheck.sampledFamilies h.2)
    hh.2.2.1 hh.2.1 h.1.2.property
  have hs := hh.2.2.2.2
  simp only [separatorScanLimit, trialScans, scheduleScans] at hs
  convert hs using 1
  rfl

/-- Bounded sampler exhaustion is charged before transporting the stronger
full-core event. No solution enters the runtime algorithm. -/
theorem bounded_runtime_core_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    1 / (inputScale R.input : ℝ) ^ 110 ≤
      (R.runtimeSampler (by omega)).boundedLaw.probability (fun o => ∃ h,
        o = some h ∧ R.runtimeData.CoreFavorable (by omega) hlog B h) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  let P := R.runtimeData.CoreFavorable (by omega) hlog B
  have hp : (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability
        (fun h => P (R.runtimeBucketEquiv (by omega) h)) := by
    apply (R.favorable_trial_probability hn hmean hden hscale B).trans
    apply FiniteLaw.probability_mono
    intro h hh
    exact R.runtime_core_favorable_of_favorable (by omega) hlog B h hh
  have hl := R.runtimeSampler_event (by omega) hscale P
  let u : ℝ := inputScale R.input
  have hu : 2 ≤ u := by
    dsimp only [u]
    exact_mod_cast (show 2 ≤ inputScale R.input by unfold inputScale; omega)
  have hu0 : 0 < u := by linarith only [hu]
  have hpow : 2 ≤ u ^ 10 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu 10
    norm_num at hh
    linarith only [hh]
  have hmargin : 1 / u ^ 110 + (1 / 10 : ℝ) / u ^ 110 ≤ (3 / 5 : ℝ) / u ^ 100 := by
    have hsmall : (11 / 10 : ℝ) ≤ (3 / 5 : ℝ) * u ^ 10 := by linarith only [hpow]
    calc
      _ = (11 / 10 : ℝ) / u ^ 110 := by ring
      _ ≤ ((3 / 5 : ℝ) * u ^ 10) / u ^ 110 :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = _ := by
        rw [show u ^ 110 = u ^ 100 * u ^ 10 by ring]
        field_simp
  change 1 / u ^ 110 ≤ _
  change (3 / 5 : ℝ) / u ^ 100 ≤ _ at hp
  change _ - (1 / 10 : ℝ) / u ^ 110 ≤ _ at hl
  linarith only [hp, hl, hmargin]

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
