import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScheduleWitness
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSeparatorJoint

namespace OAI

/-! # The concrete bucket experiment reaches YES in the full residue loop -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def ScheduleAccepted (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) : Prop :=
  (R.scheduleData h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos).run B (SeparatorCheck.sampledFamilies h.2) = true

theorem scheduleAccepted_of_bucket (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega))
    (hs : R.Successful (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h.1.1)
    (hb : R.BucketAccepted hn hlog B h) : R.ScheduleAccepted hn hlog B h := by
  let q := h.1.2.val
  have hq : 0 < q := (primeRange_prime h.1.2.property).pos
  obtain ⟨z, hz, he⟩ := R.chosen_left_lift h.1.1.1 h.1.1.2 hn hlog hs.2 q hq
  apply (R.scheduleData h.1.1.1 h.1.1.2 hn hlog q hq).run_complete B
    (SeparatorCheck.sampledFamilies h.2) z hz
  rw [R.schedule_chosen_bucket_eq h.1.1.1 h.1.1.2 hn hlog hs.2 q hq z he]
  exact hb

/-- Retain representation success so its deterministic spread test can also
be used when bounding the full prefix execution. -/
theorem schedule_joint_acceptance_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (4 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability (fun h =>
        R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h.1.1 ∧
          R.ScheduleAccepted (by omega) hlog B h) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  exact le_trans (R.bucketTrial_joint_acceptance_probability hn hmean hden hscale B)
    (FiniteLaw.probability_mono _ (by
      intro h hh
      exact ⟨hh.1, R.scheduleAccepted_of_bucket (by omega) hlog B h hh.1 hh.2⟩))

/-- The experiment reaches its designated lifted bucket in the full counter loop. -/
theorem schedule_acceptance_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (4 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability (R.ScheduleAccepted (by omega) hlog B) := by
  dsimp only
  exact (R.schedule_joint_acceptance_probability hn hmean hden hscale B).trans
    (FiniteLaw.probability_mono _ (fun _ hh => hh.2))

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
