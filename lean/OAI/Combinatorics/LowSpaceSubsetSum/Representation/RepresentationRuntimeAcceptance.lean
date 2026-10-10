import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationRuntimeLaw
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBoundedTrial

namespace OAI

/-! # Actual-target acceptance under the input-only bounded sampling law -/

noncomputable section

namespace LowSpaceSubsetSum

namespace RepresentationData

variable {n : ℕ} (D : RepresentationData n)

/-- The zero-target wrapper supplies only sampling spaces. The execution
uses `D.input`, including its original target. -/
def sampledTrial (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : D.zeroSetup.BucketTrialHistory (by omega)) : Bool :=
  D.trial h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos B (SeparatorCheck.sampledFamilies h.2)

end RepresentationData

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem runtime_sampledTrial_eq (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) :
    R.runtimeData.sampledTrial hn hlog B (R.runtimeBucketEquiv (by omega) h) =
      (R.scheduleData h.1.1.1 h.1.1.2 hn hlog h.1.2.val
        (primeRange_prime h.1.2.property).pos).run B (SeparatorCheck.sampledFamilies h.2) := by
  exact R.runtime_trial_eq h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos B (SeparatorCheck.sampledFamilies h.2)

theorem runtime_sampledTrial_accepts (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) :
    R.runtimeData.sampledTrial hn hlog B (R.runtimeBucketEquiv (by omega) h) = true ↔
      R.ScheduleAccepted hn hlog B h := by
  rw [R.runtime_sampledTrial_eq]
  rfl

/-- The executable sampled trial uses the original target, under the actual
input-only bounded sampler. The fixed solution appears only in this proof. -/
theorem bounded_runtime_acceptance_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    1 / (inputScale R.input : ℝ) ^ 110 ≤
      (R.runtimeSampler (by omega)).boundedLaw.probability (fun o => ∃ h,
        o = some h ∧ R.runtimeData.sampledTrial (by omega) hlog B h = true) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  let P := fun h : R.runtimeData.zeroSetup.BucketTrialHistory (by omega) =>
    R.runtimeData.sampledTrial (by omega) hlog B h = true
  have hp : (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability
        (fun h => P (R.runtimeBucketEquiv (by omega) h)) := by
    apply (R.favorable_trial_probability hn hmean hden hscale B).trans
    apply FiniteLaw.probability_mono
    intro h hh
    exact (R.runtime_sampledTrial_accepts (by omega) hlog B h).mpr hh.1
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
  exact (by linarith only [hp, hl, hmargin])

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
