import OAI.Combinatorics.EditApproximation.Refinement.ComputedPhysicalWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalValueBits
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCacheWords
import OAI.Combinatorics.EditApproximation.Geometry.RankedMemoStorage
import OAI.Combinatorics.EditApproximation.Numerics.RationalIntermediateBits

namespace OAI

namespace EditApproximation

noncomputable def computedFamilyTableValue (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyTableKey source target N) : ℚ :=
  physicalFamilyRequestValue source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (integerParameters N).T
    (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2 key

noncomputable def computedFamilyExpectedValue (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    Sum (ComputedFamilyScalarKey source target N (inputHeight N ^ 2))
      (ComputedFamilyTableKey source target N) → ℚ :=
  Sum.elim (fun key => (input.2 key).val) (computedFamilyTableValue source target N input)

 theorem computedFamilyTableValue_bits (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyTableKey source target N) :
    rationalEncodingBits (computedFamilyTableValue source target N input key) ≤ inputHeight N ^ 3 := by
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans
    (computed_smallLog_le_height N)
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    have h := computed_tree_depth_bound N source.length hN (by omega) hell
    nlinarith only [h, hell]
  apply (chargedRequestValue_encoding_bits source target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N + 1)
    (inputHeight N ^ 2) (inputSmallLog N) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    _ _ _ _ _ _ (by omega) hsize (fun entry => Nat.le_of_lt_succ (input.1 entry).isLt) key).trans
  exact computed_cacheWordBudget_le_cube N _ _ hH hJ (refinement_denominator_base_bits _)

 theorem computedFamilyExpectedValue_bits (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (input : ComputedFamilyInput source target N)
    (key : Sum (ComputedFamilyScalarKey source target N (inputHeight N ^ 2))
      (ComputedFamilyTableKey source target N)) :
    rationalEncodingBits (computedFamilyExpectedValue source target N input key) ≤ inputHeight N ^ 3 := by
  cases key with
  | inl key =>
    change rationalEncodingBits ((input.2 key).val : ℚ) ≤ _
    rw [rationalEncodingBits_natCast]
    have hr := computedFamilyRange_bits_le source target N (inputHeight N ^ 2) hB key
    have hc : (input.2 key).val < 2 ^ inputHeight N := by
      exact (input.2 key).isLt.trans_le
        ((Nat.le_pow_clog (by decide : 1 < 2) _).trans
          (Nat.pow_le_pow_right (by decide : 0 < 2) hr))
    have hs := Nat.size_le.mpr hc
    have hH : 2 ≤ inputHeight N := (by omega : 2 ≤ inputSmallLog N).trans
      (computed_smallLog_le_height N)
    have hsquare : inputHeight N + 2 ≤ inputHeight N ^ 2 := by nlinarith only [hH]
    have hh := hsquare.trans (pow_le_pow_right₀ (by omega : 1 ≤ inputHeight N) (by decide : 2 ≤ 3))
    omega
  | inr key => exact computedFamilyTableValue_bits source target N hN hell hsize input key

 theorem computedFamilyResult_allValues (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) (input : ComputedFamilyInput source target N) :
    BinaryMemo.AllValues (fun value => rationalEncodingBits value ≤ inputHeight N ^ 3)
      (computedFamilyResult source target N input).memory := by
  have hsmall : 200 ≤ inputSmallLog N := two_hundred_le_two_pow_thousand.trans hell
  unfold computedFamilyResult physicalFamilyMemoResult chargedRandomMemoEvaluate
  apply SourceRanked.memo_allValues (tableValue := computedFamilyTableValue source target N input)
  · intro key
    exact physicalFamilyProgram_value source target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N) _ _ _ _
      (clampedSeedNat input.1) (computedParameterP_pos N) input.2 key
  · exact computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN hsmall
  · exact computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hB
  · exact computedFamilyExpectedValue_bits source target N hN hsmall hsize hB input

 theorem computed_height_polynomial (N : ℕ) : inputHeight N ≤ (N + 2) ^ 4 := by
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith only [Nat.zero_le N]
  calc
    _ ≤ 2 ^ inputHeight N := Nat.lt_two_pow_self.le
    _ ≤ 4 * (N + 2) ^ 2 := two_pow_inputHeight_le N
    _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
    _ = _ := by rw [← pow_add]

 theorem computedFamilyResult_retained_storage (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) (input : ComputedFamilyInput source target N) :
    (computedFamilyResult source target N input).memory.rationalStorage ≤ (N + 2) ^ 65556 := by
  have hvalues := computedFamilyResult_allValues source target N hN hell hsize hB input
  have hs := BinaryMemo.rationalStorage_le _ (inputHeight N ^ 3) hvalues
  have hn : (computedFamilyResult source target N input).memory.nodes ≤ (N + 2) ^ 65542 :=
    Nat.le_trans (Nat.le_succ _) (physicalFamilyMemo_nodes_polynomial source target N
      (integerParameters N).P (integerParameters N).T (integerParameters N).S (inputHeight N)
      (Nat.two_pow_pos _) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
      (finalTargetState target.length) input)
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith only [Nat.zero_le N]
  have hh := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hh
  change inputHeight N ^ 3 ≤ (N + 2) ^ 12 at hh
  have h12 : 1 ≤ (N + 2) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hw : inputHeight N ^ 3 + 3 ≤ (N + 2) ^ 14 := by
    calc
      _ ≤ 4 * (N + 2) ^ 12 := by omega
      _ ≤ (N + 2) ^ 2 * (N + 2) ^ 12 := Nat.mul_le_mul_right _ h4
      _ = _ := by rw [← pow_add]
  calc
    _ ≤ (inputHeight N ^ 3 + 3) * (computedFamilyResult source target N input).memory.nodes := hs
    _ ≤ (N + 2) ^ 14 * (N + 2) ^ 65542 := Nat.mul_le_mul hw hn
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
