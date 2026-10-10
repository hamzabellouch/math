import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationQueryBound
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationScanTrial

namespace OAI

/-! # Simultaneous acceptance, reader work, and separator scan bounds -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

def trialQueries (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) : ℕ :=
  R.scheduleQueries h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (primeRange_prime h.1.2.property).pos B

/-- These work bounds refer to the entire hypothetical execution, including
prefixes and counter iterations skipped after an early YES. -/
def FavorableTrial (hn : 20000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) : Prop :=
  R.ScheduleAccepted (by omega) hlog B h ∧
    mixerSpreadTest (R.signedWeights h.1.1.1.1.1.1) (R.orderedMixers h.1.1.1.1.1.1) n ∧
    R.AllocatedResourceGood hn hlog h.1.1 ∧
    (R.trialQueries hn hlog B h : ℝ) ≤
      (inputScale R.input : ℝ) ^ 408 * (2 : ℝ) ^ ((n : ℝ) / 2) ∧
    R.trialScans hn hlog B h ≤ R.separatorScanLimit

theorem favorable_trial_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (3 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability (R.FavorableTrial (by omega) hlog B) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  apply (R.schedule_joint_acceptance_with_scan_budget hn hmean hden hscale B).trans
  apply FiniteLaw.probability_mono
  intro h hh
  have hspread := R.successful_spread _ hh.1.1
  refine ⟨hh.1.2, hspread, hh.2.1, ?_, ?_⟩
  · exact R.schedule_queries_half h.1.1.1 h.1.1.2 (by omega) hlog h.1.2.val
      (primeRange_prime h.1.2.property).pos B hh.2.1 hspread h.1.2.property
  · have hs := hh.2.2.trans R.separatorScanBudget_le_limit
    exact_mod_cast hs

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
