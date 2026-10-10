import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryCorrect
import OAI.Combinatorics.EditApproximation.Queries.QueryHistorySemantic

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Uniform magnitude bound for every table, independently of accuracy. -/
theorem computedFamilyTableValue_abs_le (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (input : ComputedFamilyInput source target N) (key : ComputedFamilyTableKey source target N) :
    |computedFamilyTableValue source target N input key| ≤ (((32 * inputSmallLog N + 1) * N : ℕ) : ℚ) := by
  cases key with
  | inl entry =>
    change |(clampedSeedNat input.1 entry : ℚ)| ≤ _
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (show clampedSeedNat input.1 entry ≤ (32 * inputSmallLog N + 1) * N from
      (Nat.le_of_lt_succ (input.1 entry).isLt).trans (by nlinarith))
  | inr request =>
    unfold computedFamilyTableValue physicalFamilyRequestValue chargedRequestValue
    have hb := localRequestValue_bounds (R := inputHeight N ^ 2) source target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (integerParameters N).T (integerParameters N).S (inputHeight N ^ 2)
      (scheduledSeedFactor N) (scheduledSeedMultiplier N)
      (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
      (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
      (physicalFamilyGroup target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2) input.2)
      (physicalFamilyInteger source target N (integerParameters N).P (inputSmallLog N)
        (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (integerParameters N).T
        (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
        (scheduledSeedFactor N) (scheduledSeedMultiplier N)
        (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
        (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
        (computedParameterP_pos N) input.2 (clampedSeedNat input.1))
      (clampedSeedNat input.1) (by change 0 ≤ 1 / (inputSmallLog N : ℚ) ^ 10; positivity) request.val
    rw [abs_of_nonneg hb.1]
    exact hb.2.trans (by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
        stageInitial_upper_all_seeds source target _ N (integerParameters N).P (inputSmallLog N)
          (scheduledSeedFactor N request.val.pass) hsize (request.val.node, request.val.state))

theorem computedQueryMemoNormalized_width (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
    (hsize : source.length + target.length ≤ N)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (key : ComputedFamilyMemoKey source target N) :
    (rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
      (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) key).width ≤
        inputHeight N ^ 3 := by
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hbase := computed_refinementBase_length N (inputSmallLog N).bits (bitWordValue_bits _)
  change (computedQueryBase N).length ≤ 10 * Nat.size (inputSmallLog N) + 3 at hbase
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    have h := computed_tree_depth_bound N source.length hN (by omega) hell
    nlinarith only [h, hell]
  cases key with
  | inl key =>
    have hr := computedFamilyRange_bits_le source target N (inputHeight N ^ 2) hMass key
    have hc : (input.2 key).val < 2 ^ inputHeight N := (input.2 key).isLt.trans_le
      ((Nat.le_pow_clog (by decide : 1 < 2) _).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) hr))
    have hv : |computedFamilyExpectedValue source target N input (.inl key)| ≤
        ((2 ^ inputHeight N : ℕ) : ℚ) := by
      change |((input.2 key).val : ℚ)| ≤ _
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hc.le
    have hw := computedQueryMemoNormalized_width_bound source target N occurrence symbolBits positionBits
      input hf hs ht hp htable (.inl key) (2 ^ inputHeight N) hv
    simp only [queryFamilyMemoRemaining, Nat.zero_mul, Nat.zero_add, Nat.mul_one,
      Nat.size_pow] at hw
    have hsquare : inputHeight N + 4 ≤ inputHeight N ^ 2 := by nlinarith only [hH]
    have hcub := hsquare.trans (Nat.pow_le_pow_right (by omega : 0 < inputHeight N) (by decide : 2 ≤ 3))
    omega
  | inr key =>
    have hw := computedQueryMemoNormalized_width_bound source target N occurrence symbolBits positionBits
      input hf hs ht hp htable (.inr key) ((32 * inputSmallLog N + 1) * N)
      (computedFamilyTableValue_abs_le source target N hsize input key)
    have hr : queryFamilyMemoRemaining (R := inputHeight N ^ 2) target N (integerParameters N).P (inputSmallLog N)
        (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (.inr key) ≤ inputHeight N := by
      cases key with
      | inl entry => exact Nat.zero_le _
      | inr request => exact (Nat.sub_le _ _).trans hJ
    have hm := Nat.mul_le_mul_right (computedQueryBase N).length hr
    have hb := computed_cacheWordBudget_le_cube N (inputHeight N) (computedQueryBase N).length hH le_rfl hbase
    simp only [Nat.mul_assoc] at hb
    omega

end EditApproximation

end OAI
