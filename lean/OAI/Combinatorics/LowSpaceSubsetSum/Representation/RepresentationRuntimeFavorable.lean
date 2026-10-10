import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRuntimeAcceptance

namespace OAI

/-! # Joint runtime acceptance and full-execution budgets

All counters below are defined on the input-only schedule. The fixed solution
is used only to transfer the analyzed favorable event through the exact
sign-coordinate bijection and the bounded sampler coupling.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace RepresentationScheduleData

variable {n g : ℕ} (D : RepresentationScheduleData n g)

def queryCount (B : ℕ) : ℕ :=
  ∑ side : Fin 2, ∑ z : Fin D.q,
    (D.parentData side z.val).queryVisits B D.topOrder MaskRestriction.empty

def scanCount (B : ℕ) (families : Fin 4 → Array (Finset (Fin g))) : ℕ :=
  ∑ z : Fin D.q, D.coordinates.totalScans families D.target ((D.bucket z.val).checkList B)

end RepresentationScheduleData

namespace RepresentationData

variable {n : ℕ} (D : RepresentationData n)

def sampledQueries (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : ℕ :=
  (D.scheduleData h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos).queryCount B

def sampledScans (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : ℕ :=
  (D.scheduleData h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos).scanCount B (SeparatorCheck.sampledFamilies h.2)

/-- The two budgets cover the entire hypothetical execution; an early stop
can only remove operations. Sampler exhaustion is not a favorable output. -/
def RuntimeFavorable (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : Prop :=
  D.sampledTrial hn hlog B h = true ∧
    (D.sampledQueries hn hlog B h : ℝ) ≤
      (inputScale D.input : ℝ) ^ 408 * (2 : ℝ) ^ ((n : ℝ) / 2) ∧
    D.sampledScans hn hlog B h ≤ inputScale D.input ^ 328 * 2 ^ ((n + 1) / 2)

end RepresentationData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem runtime_sampledQueries_eq (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) :
    R.runtimeData.sampledQueries (by omega) hlog B (R.runtimeBucketEquiv (by omega) h) =
      R.trialQueries hn hlog B h := by
  change (R.runtimeData.scheduleData (R.runtimeHistory h.1.1.1) h.1.1.2
    (by omega) hlog h.1.2.val (primeRange_prime h.1.2.property).pos).queryCount B = _
  rw [R.runtime_schedule_eq]
  rfl

theorem runtime_sampledScans_eq (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) :
    R.runtimeData.sampledScans (by omega) hlog B (R.runtimeBucketEquiv (by omega) h) =
      R.trialScans hn hlog B h := by
  change (R.runtimeData.scheduleData (R.runtimeHistory h.1.1.1) h.1.1.2
    (by omega) hlog h.1.2.val (primeRange_prime h.1.2.property).pos).scanCount B
      (SeparatorCheck.sampledFamilies h.2) = _
  rw [R.runtime_schedule_eq]
  rfl

theorem runtime_favorable_of_favorable (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega))
    (hh : R.FavorableTrial hn hlog B h) :
    R.runtimeData.RuntimeFavorable (by omega) hlog B
      (R.runtimeBucketEquiv (by omega) h) := by
  refine ⟨(R.runtime_sampledTrial_accepts (by omega) hlog B h).mpr hh.1, ?_, ?_⟩
  · rw [R.runtime_sampledQueries_eq hn]
    exact hh.2.2.2.1
  · rw [R.runtime_sampledScans_eq hn]
    simpa only [separatorScanLimit, runtimeData] using hh.2.2.2.2

/-- One bounded run simultaneously accepts and meets both deterministic
watchdog budgets with the required inverse-polynomial probability. -/
theorem bounded_runtime_favorable_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    1 / (inputScale R.input : ℝ) ^ 110 ≤
      (R.runtimeSampler (by omega)).boundedLaw.probability (fun o => ∃ h,
        o = some h ∧ R.runtimeData.RuntimeFavorable (by omega) hlog B h) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  let P := R.runtimeData.RuntimeFavorable (by omega) hlog B
  have hp : (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability
        (fun h => P (R.runtimeBucketEquiv (by omega) h)) := by
    apply (R.favorable_trial_probability hn hmean hden hscale B).trans
    apply FiniteLaw.probability_mono
    intro h hh
    exact R.runtime_favorable_of_favorable (by omega) hlog B h hh
  have hl := R.runtimeSampler_event (by omega) hscale P
  let u : ℝ := inputScale R.input
  have hu : 2 ≤ u := by
    dsimp only [u]
    exact_mod_cast (show 2 ≤ inputScale R.input by unfold inputScale; omega)
  have hu0 : 0 < u := by linarith
  have hpow : 2 ≤ u ^ 10 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu 10
    norm_num at hh
    linarith
  have hmargin : 1 / u ^ 110 + (1 / 10 : ℝ) / u ^ 110 ≤ (3 / 5 : ℝ) / u ^ 100 := by
    have hsmall : (11 / 10 : ℝ) ≤ (3 / 5 : ℝ) * u ^ 10 := by linarith
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
