import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScanBound
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleTrial

namespace OAI

/-! # Averaging the schedule scan tail over the actual dependent experiment -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

open scoped BigOperators

variable {n : ℕ} (R : RepresentationSetup n)

def trialScans (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) : ℕ :=
  R.scheduleScans h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos B (SeparatorCheck.sampledFamilies h.2)

theorem bucketTrial_resource_failure (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    (R.bucketTrialLaw (by omega)).probability
      (fun h => ¬R.AllocatedResourceGood hn hlog h.1.1) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by
  have hf := R.actual_joint_resource_failure hn hlog
    (by unfold inputScale; omega : 256 ≤ inputScale R.input) (fun _ => True)
  calc
    _ = (R.extraTrialLaw (by omega)).probability
        (fun h => ¬R.AllocatedResourceGood hn hlog h.1) :=
      FiniteLaw.bind_first_probability (R.extraTrialLaw (by omega))
        (fun h => R.SeparatorDraws h.1.1 (by omega))
        (fun h => R.separatorLaw h.1.1 (by omega))
        (fun h => ¬R.AllocatedResourceGood hn hlog h.1)
    _ = R.trialLaw.probability (fun h => ¬R.AllocatedResourceGood hn hlog h) :=
      FiniteLaw.bind_first_probability R.trialLaw
        (fun h => R.ExtraPrimeSpace h.1.1.1.1)
        (fun h => R.extraPrimeLaw h.1.1.1.1 (by omega))
        (fun h => ¬R.AllocatedResourceGood hn hlog h)
    _ ≤ _ := by simpa only [true_and] using hf

/-- One conditional Markov estimate suffices for all buckets and all prefix
checks using the same sampled separator families. -/
theorem bucketTrial_scan_failure (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) (B : ℕ) :
    (R.bucketTrialLaw (by omega)).probability (fun h =>
      R.AllocatedResourceGood hn hlog h.1.1 ∧
        R.separatorScanBudget < (R.trialScans hn hlog B h : ℝ)) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by
  classical
  rw [bucketTrialLaw, FiniteLaw.bind_probability]
  let δ : ℝ := (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  calc
    _ ≤ ∑ h : R.ExtraTrialHistory, (R.extraTrialLaw (by omega)).mass h * δ := by
      apply Finset.sum_le_sum
      intro h _
      by_cases hg : R.AllocatedResourceGood hn hlog h.1
      · apply mul_le_mul_of_nonneg_left _ ((R.extraTrialLaw (by omega)).nonneg h)
        simpa only [trialScans, hg, true_and] using
          R.schedule_scan_tail h.1.1 h.1.2 hn hlog h.2.val
            (primeRange_prime h.2.property).pos hg B
      · simp only [hg, false_and, FiniteLaw.probability, ite_false,
          Finset.sum_const_zero, mul_zero]
        exact mul_nonneg ((R.extraTrialLaw (by omega)).nonneg h) hδ
    _ = δ := by rw [← Finset.sum_mul, (R.extraTrialLaw (by omega)).total, one_mul]

/-- The concrete schedule still succeeds while retaining the resource event
and respecting the scan watchdog threshold. Other operation charges can be
combined with this event separately. -/
theorem schedule_joint_acceptance_with_scan_budget (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability (fun h =>
        (R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h.1.1 ∧
          R.ScheduleAccepted (by omega) hlog B h) ∧
        R.AllocatedResourceGood (by omega) hlog h.1.1 ∧
        (R.trialScans (by omega) hlog B h : ℝ) ≤ R.separatorScanBudget) := by
  classical
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  let μ := R.bucketTrialLaw (by omega)
  let A := fun h : R.BucketTrialHistory (by omega) =>
    R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h.1.1 ∧
      R.ScheduleAccepted (by omega) hlog B h
  let G := fun h : R.BucketTrialHistory (by omega) =>
    R.AllocatedResourceGood (by omega) hlog h.1.1
  let T := fun h : R.BucketTrialHistory (by omega) =>
    R.separatorScanBudget < (R.trialScans (by omega) hlog B h : ℝ)
  have ha : (4 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤ μ.probability A :=
    R.schedule_joint_acceptance_probability hn hmean hden hscale B
  have hg : μ.probability (fun h => ¬G h) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 :=
    R.bucketTrial_resource_failure (by omega) hlog
  have ht : μ.probability (fun h => G h ∧ T h) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 :=
    R.bucketTrial_scan_failure (by omega) hlog B
  have hsplit : μ.probability A ≤ μ.probability (fun h => A h ∧ G h ∧ ¬T h) +
      μ.probability (fun h => ¬G h) + μ.probability (fun h => G h ∧ T h) := by
    rw [FiniteLaw.probability, FiniteLaw.probability, FiniteLaw.probability,
      FiniteLaw.probability, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h _
    by_cases hA : A h <;> by_cases hG : G h <;> by_cases hT : T h <;>
      simp [hA, hG, hT, μ.nonneg h]
  change (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
    μ.probability (fun h => A h ∧ G h ∧ _)
  have he : (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 =
      (4 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 -
        (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 -
        (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by ring
  have hl : (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      μ.probability (fun h => A h ∧ G h ∧ ¬T h) := by linarith
  simpa only [T, not_lt] using hl

theorem schedule_acceptance_with_scan_budget (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability (fun h =>
        R.ScheduleAccepted (by omega) hlog B h ∧
        R.AllocatedResourceGood (by omega) hlog h.1.1 ∧
        (R.trialScans (by omega) hlog B h : ℝ) ≤ R.separatorScanBudget) := by
  dsimp only
  exact (R.schedule_joint_acceptance_with_scan_budget hn hmean hden hscale B).trans
    (FiniteLaw.probability_mono _ (fun _ hh => ⟨hh.1.2, hh.2⟩))

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
