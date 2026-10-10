import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationBucketWitness

namespace OAI

/-! # Independent separator draws complete the concrete representation trial -/

noncomputable section

namespace LowSpaceSubsetSum

private theorem separator_coverage_ninety_nine :
    (99 / 100 : ℝ) ≤ 1 - 4 * Real.exp (-10) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (1024 : ℝ) ≤ Real.exp 10 := by
    calc
      (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
      _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) he 10
      _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
  have hinv : Real.exp (-10) ≤ (1 / 1024 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hp
  linarith

namespace RepresentationSetup

variable {n : ℕ} (R : RepresentationSetup n)

abbrev SeparatorDraws (h : R.PrimeHistory) (hn : 2200 ≤ n) :=
  SeparatorCheck.Draws (2 * blockHalf n 0)
    (separatorParameters h.1.1.2 hn).e (separatorParameters h.1.1.2 hn).c

def separatorLaw (h : R.PrimeHistory) (hn : 2200 ≤ n) : FiniteLaw (R.SeparatorDraws h hn) := by
  let S := separatorParameters h.1.1.2 hn
  let (i : Fin 4) : Nonempty
      (SeparatorSample (Finset.univ : Finset (Fin (2 * blockHalf n 0))) (S.e i)) :=
    (Finset.powersetCard_nonempty.mpr (by simpa only [Finset.card_univ, Fintype.card_fin]
      using (S.size_le i))).to_subtype
  exact FiniteLaw.uniform

/-- Coverage applies to the actual designated indexed masks. Its law is
independent after all earlier choices, even though its sizes depend on them. -/
theorem chosen_separator_coverage (h : R.PrimeHistory) (r : R.Residues h.2)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (hr : R.ResidueSuccess (R.actualOffsets (R.allocatedChildAssignment hn hlog)) h r) :
    (99 / 100 : ℝ) ≤ (R.separatorLaw h (by omega)).probability (fun draws =>
      SeparatorCheck.Covered (SeparatorCheck.sampledFamilies draws)
        ((R.topCoordinates h.1.1.1 h.1.2).encodeEntry (R.chosenEntry h r hn hlog 0))
        ((R.topCoordinates h.1.1.1 h.1.2).encodeEntry (R.chosenEntry h r hn hlog 1))) := by
  let S := separatorParameters h.1.1.2 (by omega)
  let (i : Fin 4) : Nonempty
      (SeparatorSample (Finset.univ : Finset (Fin (2 * blockHalf n 0))) (S.e i)) :=
    (Finset.powersetCard_nonempty.mpr (by simpa only [Finset.card_univ, Fintype.card_fin]
      using (S.size_le i))).to_subtype
  rw [separatorLaw, FiniteLaw.uniform_probability]
  apply separator_coverage_ninety_nine.trans
  apply (R.topCoordinates h.1.1.1 h.1.2).coverage_probability S
    (R.chosenEntry h r hn hlog 0) (R.chosenEntry h r hn hlog 1)
    (R.chosenEntries_match h r hn hlog hr).2.1
  · intro i
    simpa only [ite_true] using R.chosenEntry_separator_count h r hn hlog hr 0 i
  · intro i
    have hc := R.chosenEntry_separator_count h r hn hlog hr 1 i
    rw [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)] at hc
    rw [hc]
    exact Nat.add_sub_of_le (S.count_half i)

abbrev BucketTrialHistory (hn : 2200 ≤ n) :=
  Σ h : R.ExtraTrialHistory, R.SeparatorDraws h.1.1 hn

def bucketTrialLaw (hn : 10000 ≤ n) : FiniteLaw (R.BucketTrialHistory (by omega)) :=
  (R.extraTrialLaw (by omega)).bind (fun h => R.SeparatorDraws h.1.1 (by omega))
    (fun h => R.separatorLaw h.1.1 (by omega))

theorem extraTrial_modulus_pos (h : R.ExtraTrialHistory) :
    0 < (prefixModulus h.1.1.2.val 0 : ℤ) * h.2.val := by
  apply mul_pos
  · exact_mod_cast prefixModulus_pos h.1.1.2 0
  · exact_mod_cast (primeRange_prime h.2.property).pos

def BucketAccepted (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000)
    (B : ℕ) (h : R.BucketTrialHistory (by omega)) : Prop :=
  (R.chosenBucketData h.1.1.1 h.1.1.2 hn hlog h.1.2.val
    (R.extraTrial_modulus_pos h.1)).run B (SeparatorCheck.sampledFamilies h.2) = true

/-- The actual finite experiment, including its separator families and its
prefix search, accepts with inverse-polynomial probability. -/
theorem bucketTrial_acceptance_probability (hn : 180000000 ≤ n)
    (hmean : meanDeficiency R.originalWeights Finset.univ R.halfSize <
      (153 / 20000 : ℝ) * n)
    (hden : (R.halfSize : ℝ) + 1 <
      (2 : ℝ) ^ ((1 / 1500 : ℝ) * R.halfSize))
    (hscale : Real.logb 2 (inputScale R.input : ℝ) ≤ (n : ℝ) / 1000000000) (B : ℕ) :
    let hlog := representation_log_budget (by omega : 10000 ≤ n)
      R.mixerSize_add_one_le_scale hscale
    (4 / 5 : ℝ) / (inputScale R.input : ℝ) ^ 100 ≤
      (R.bucketTrialLaw (by omega)).probability (R.BucketAccepted (by omega) hlog B) := by
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
      (R.bucketTrialLaw (by omega)).probability (R.BucketAccepted (by omega) hlog B) := by
    apply FiniteLaw.probability_mono
    intro h hh
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

end RepresentationSetup
end LowSpaceSubsetSum

end

end OAI
