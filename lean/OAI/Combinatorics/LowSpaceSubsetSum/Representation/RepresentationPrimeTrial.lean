import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationChosenCollector

namespace OAI

/-! # The extra-prime experiment retains actual fitting solution buckets -/

noncomputable section

namespace LowSpaceSubsetSum.RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

/-- Preserve the residue-success witness while subtracting resource failure. -/
theorem allocated_successful_with_resources (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (9 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      R.trialLaw.probability (fun h =>
        R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h ∧
        R.AllocatedResourceGood (by omega) hlog h) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  let P := R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog))
  let Q := R.AllocatedResourceGood (by omega) hlog
  have hs : 1 / (inputScale R.input : ℝ) ^ 100 ≤ R.trialLaw.probability P :=
    R.successful_probability _ hn hmean hden
  have hu : 256 ≤ inputScale R.input := by unfold inputScale; omega
  have hf := R.actual_joint_resource_failure (by omega) hlog hu (fun _ => True)
  have hf' : R.trialLaw.probability (fun h => ¬Q h) ≤
      (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by
    simpa only [true_and] using hf
  have hi := R.trialLaw.probability_inter_ge_sub P Q
  change (9 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
    R.trialLaw.probability (fun h => P h ∧ Q h)
  calc
    (9 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 =
        1 / (inputScale R.input : ℝ) ^ 100 -
          (1 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 := by ring
    _ ≤ R.trialLaw.probability P - R.trialLaw.probability (fun h => ¬Q h) :=
      sub_le_sub hs hf'
    _ ≤ _ := hi

abbrev ExtraTrialHistory := Σ h : R.TrialHistory, R.ExtraPrimeSpace h.1.1.1.1

/-- The prime is drawn after the earlier layout, families, nested primes,
and low residues; its law depends only on the prescribed layout parameter. -/
def extraTrialLaw (hn : 100 ≤ n) : FiniteLaw R.ExtraTrialHistory :=
  R.trialLaw.bind (fun h => R.ExtraPrimeSpace h.1.1.1.1)
    (fun h => R.extraPrimeLaw h.1.1.1.1 hn)

def PrimeBucketFits (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (h : R.ExtraTrialHistory) : Prop :=
  let z := h.1.1
  let r := h.1.2
  let p := (prefixModulus z.2.val 0 : ℤ) * h.2.val
  (R.chosenParentBucket z r hn hlog 0 p).card ≤ compressionDictionaryCapacity n ∧
    ((R.chosenParentBucket z r hn hlog 1 p).filter
      (fun e => e.mask = (R.chosenEntry z r hn hlog 1).mask)).card ≤
        compressionDictionaryCapacity n

/-- The ideal experiment now includes the actual extra-prime sampler and
both dictionary-capacity events. All success factors are derived. -/
theorem extraTrial_success_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (81 / 100 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.extraTrialLaw (by omega)).probability (fun h =>
        (R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h.1 ∧
          R.AllocatedResourceGood (by omega) hlog h.1) ∧
        R.PrimeBucketFits (by omega) hlog h) := by
  dsimp only
  let hlog := representation_log_budget (by omega : 10000 ≤ n)
    R.mixerSize_add_one_le_scale hscale
  let P := fun h =>
    R.Successful (R.actualOffsets (R.allocatedChildAssignment (by omega) hlog)) h ∧
      R.AllocatedResourceGood (by omega) hlog h
  have hp : (9 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤ R.trialLaw.probability P :=
    R.allocated_successful_with_resources hn hmean hden hscale
  have hq : ∀ h, P h → (9 / 10 : ℝ) ≤
      (R.extraPrimeLaw h.1.1.1.1 (by omega)).probability
        (fun q => R.PrimeBucketFits (by omega) hlog ⟨h, q⟩) := by
    intro h hh
    exact R.chosenBuckets_law_probability h.1 h.2 (by omega) hlog hh.1.2 hh.2
      (R.successful_spread _ hh.1) hscale (R.chosenEntry h.1 h.2 (by omega) hlog 1).mask
  have hb := FiniteLaw.bind_good_lower R.trialLaw
    (fun h => R.ExtraPrimeSpace h.1.1.1.1) (fun h => R.extraPrimeLaw h.1.1.1.1 (by omega))
    P (fun h q => R.PrimeBucketFits (by omega) hlog ⟨h, q⟩)
    (by norm_num : (0 : ℝ) ≤ 9 / 10) hp hq
  calc
    (81 / 100 : ℝ) / (inputScale R.input : ℝ) ^ 100 =
      ((9 / 10 : ℝ) / (inputScale R.input : ℝ) ^ 100) * (9 / 10) := by ring
    _ ≤ _ := by simpa only [extraTrialLaw, P, Sigma.eta] using hb

end LowSpaceSubsetSum.RepresentationSetup

end

end OAI
