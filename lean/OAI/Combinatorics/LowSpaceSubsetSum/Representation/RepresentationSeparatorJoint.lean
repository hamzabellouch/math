import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationSeparatorTrial

namespace OAI

/-! # Joint survival and acceptance for the actual separator trial

The surviving representation is retained in the probability event so that
its designated lifted residue can be located in the input-only schedule.
-/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

theorem bucketTrial_joint_acceptance_probability (hn : 180000000 ≤ n)
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
          R.BucketAccepted (by omega) hlog B h) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  let P := fun h : R.ExtraTrialHistory =>
    (R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h.1 ∧
      R.AllocatedResourceGood (by omega) hlog h.1) ∧ R.PrimeBucketFits (by omega) hlog h
  let Q := fun (h : R.ExtraTrialHistory) (draws : R.SeparatorDraws h.1.1 (by omega)) =>
    SeparatorCheck.Covered (SeparatorCheck.sampledFamilies draws)
      ((R.topCoordinates h.1.1.1.1.1 h.1.1.1.2).encodeEntry
        (R.chosenEntry h.1.1 h.1.2 (by omega) hlog 0))
      ((R.topCoordinates h.1.1.1.1.1 h.1.1.1.2).encodeEntry
        (R.chosenEntry h.1.1 h.1.2 (by omega) hlog 1))
  have hp : (81 / 100 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.extraTrialLaw (by omega)).probability P :=
    R.extraTrial_success_probability hn hmean hden hscale
  have hq : ∀ h, P h → (99 / 100 : ℝ) ≤
      (R.separatorLaw h.1.1 (by omega)).probability (Q h) := by
    intro h hh
    exact R.chosen_separator_coverage h.1.1 h.1.2 (by omega) hlog hh.1.1.2
  have hb := FiniteLaw.bind_good_lower (R.extraTrialLaw (by omega))
    (fun h => R.SeparatorDraws h.1.1 (by omega)) (fun h => R.separatorLaw h.1.1 (by omega))
    P Q (by norm_num : (0 : ℝ) ≤ 99 / 100) hp hq
  have hm : (R.bucketTrialLaw (by omega)).probability (fun h => P h.1 ∧ Q h.1 h.2) ≤
      (R.bucketTrialLaw (by omega)).probability (fun h =>
        R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h.1.1 ∧
          R.BucketAccepted (by omega) hlog B h) := by
    apply FiniteLaw.probability_mono
    intro h hh
    refine ⟨hh.1.1.1, ?_⟩
    exact R.chosenBucket_accepts h.1.1.1 h.1.1.2 (by omega) hlog hh.1.1.1.2
      h.1.2.val (R.extraTrial_modulus_pos h.1) B (SeparatorCheck.sampledFamilies h.2)
      hh.1.2.1 hh.1.2.2 hh.2
  have hpos : (0 : ℝ) ≤ 1 / (inputScale R.input : ℝ) ^ 100 := by positivity
  calc
    (4 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
        ((81 / 100 : ℝ) / (inputScale R.input : ℝ) ^ 100) * (99 / 100) := by
      have h := mul_le_mul_of_nonneg_right
        (by norm_num : (4 / 5 : ℝ) ≤ (81 / 100) * (99 / 100)) hpos
      convert h using 1 <;> ring
    _ ≤ (R.bucketTrialLaw (by omega)).probability (fun h => P h.1 ∧ Q h.1 h.2) := hb
    _ ≤ _ := hm


end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
