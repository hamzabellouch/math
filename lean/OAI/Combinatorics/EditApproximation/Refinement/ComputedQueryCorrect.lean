import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryMemo
import OAI.Combinatorics.EditApproximation.Refinement.ComputedRetainedValues

namespace OAI

namespace EditApproximation

attribute [local instance] queryArityNeZero queryRoundsNeZero

theorem computedQueryParameters_values (N pass : ℕ) (hf : 3 ≤ smallLogExponent N)
    (hpass : pass ≤ computedSeedPassCount N) :
    (computedQueryParameters N pass).tau.value = (rationalParameters (inputSmallLog N)).tau ∧
    (computedQueryParameters N pass).factor.value = refinementFactor (scheduledSeedFactor N pass) (inputSmallLog N) ∧
    (computedQueryParameters N pass).eta.value = (rationalParameters (inputSmallLog N)).eta ∧
    (computedQueryParameters N pass).kappa.value = (rationalParameters (inputSmallLog N)).kappa ∧
    (computedQueryParameters N pass).delta.value = (rationalParameters (inputSmallLog N)).delta :=
  refinementParameterWordsWithWork_values N pass (inputSmallLog N).bits _ (bitWordValue_bits _) hf hpass

noncomputable def computedQueryReference (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyMemoKey source target N) :=
  SourceRanked.body ChargedPhysicalRequest.rank
    (physicalFamilyProgram source target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N)
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
      (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
      (clampedSeedNat input.1))
    (physicalFamilyAnswer target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) input.2) key

theorem computedQueryMemoNormalized_correct (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hf : 3 ≤ smallLogExponent N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (key : ComputedFamilyMemoKey source target N) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) key).value =
        computedFamilyExpectedValue source target N input key ∧
    BitQuery.RefinesOn
      (fun child => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
        (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) child.val)
      (fun word value => word.value = value)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input key)
      (computedQueryReference source target N input key) := by
  have hv := computedQueryParameters_values N 0 hf (Nat.zero_le _)
  have ha (pass : ℕ) (hpass : pass ≤ computedSeedPassCount N) :
      (computedQueryParameters N pass).factor.value =
        refinementFactor (scheduledSeedWordWithWork N pass).1.value (inputSmallLog N) := by
    rw [scheduledSeedWordWithWork_value]
    exact (computedQueryParameters_values N pass hf hpass).2.1
  have hd : (computedQueryParameters N 0).delta.value = 1 / (inputSmallLog N : ℚ) ^ 10 := hv.2.2.2.2
  have h := queryFamilyMemoNormalized_correct source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1) (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0)) input.2
    (clampedSeedNat input.1) ha hs ht hp htable (fun entry => BinaryFraction.nat_value _)
    (inputSmallLog N) (Nat.two_pow_pos _) hd (computedQueryBase N) (computedQueryBase_value N) key
  simp only [queryFamilyMemoNormalized, computedQueryMemoNormalized,
    computedQueryReference, computedFamilyExpectedValue,
    SourceRanked.value, scheduledSeedWordWithWork_value,
    hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2] at h ⊢
  exact h

/-- Width of the actual stored word. -/
theorem computedQueryMemoNormalized_width_bound (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hf : 3 ≤ smallLogExponent N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (key : ComputedFamilyMemoKey source target N) (V : ℕ)
    (hV : |computedFamilyExpectedValue source target N input key| ≤ (V : ℚ)) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) key).width ≤
      Nat.size V + 2 * (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
        (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key *
          (computedQueryBase N).length + 1) + 1 := by
  have hV' := hV
  simp only [computedFamilyExpectedValue] at hV'
  have hv := computedQueryParameters_values N 0 hf (Nat.zero_le _)
  have ha (pass : ℕ) (hpass : pass ≤ computedSeedPassCount N) :
      (computedQueryParameters N pass).factor.value =
        refinementFactor (scheduledSeedWordWithWork N pass).1.value (inputSmallLog N) := by
    rw [scheduledSeedWordWithWork_value]
    exact (computedQueryParameters_values N pass hf hpass).2.1
  have hd : (computedQueryParameters N 0).delta.value = 1 / (inputSmallLog N : ℚ) ^ 10 := hv.2.2.2.2
  have h := queryFamilyMemoNormalized_width source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1) (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits
    (fun entry => (BinaryFraction.nat (clampedSeedNat input.1 entry), 0)) input.2
    (clampedSeedNat input.1) ha hs ht hp htable (fun entry => BinaryFraction.nat_value _)
    (inputSmallLog N) (Nat.two_pow_pos _) hd (computedQueryBase N) (computedQueryBase_value N) key (computedQueryBase N).length V le_rfl (by
      simp only [SourceRanked.value, scheduledSeedWordWithWork_value,
        hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
      exact hV')
  simp only [computedQueryMemoNormalized] at h ⊢
  exact h

end EditApproximation

end OAI
