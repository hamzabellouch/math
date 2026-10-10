import OAI.Combinatorics.EditApproximation.Refinement.ComputedPhysicalUniform
import OAI.Combinatorics.EditApproximation.Refinement.ComputedWidthEnvelope
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyRejectionWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedFamilySampling
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

open Filter MeasureTheory

private theorem power_succ_add_one (x : ℝ) (hx : 2 ≤ x) (n : ℕ) :
    x ^ n + 1 ≤ x ^ (n + 1) := by
  have hnonneg : 0 ≤ x ^ n := pow_nonneg (by linarith) _
  have hone : 1 ≤ x ^ n := one_le_pow₀ (by linarith)
  calc
    _ ≤ x ^ n + x ^ n := add_le_add le_rfl hone
    _ = x ^ n * 2 := by ring
    _ ≤ x ^ n * x := mul_le_mul_of_nonneg_left hx hnonneg
    _ = _ := (pow_succ _ _).symm

private theorem rejection_factor_le (x : ℝ) (hx : 2 ≤ x) (n : ℕ) :
    2 * (x ^ n + 1) * x ≤ x ^ (n + 3) := by
  have hnonneg : 0 ≤ x := by linarith
  have hone : 1 ≤ x ^ n := one_le_pow₀ (by linarith)
  have hsum : x ^ n + 1 ≤ 2 * x ^ n := by linarith
  have hsquare : 4 ≤ x ^ 2 := by nlinarith only [hx]
  calc
    _ ≤ 2 * (2 * x ^ n) * x := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (by norm_num)) hnonneg
    _ = 4 * x ^ (n + 1) := by rw [pow_succ]; ring
    _ ≤ x ^ 2 * x ^ (n + 1) := mul_le_mul_of_nonneg_right hsquare (pow_nonneg hnonneg _)
    _ = x ^ (2 + (n + 1)) := (pow_add _ _ _).symm
    _ = _ := by congr 1; omega

private theorem dictionary_factor_le (H : ℕ) (hH : 32780 ≤ H) :
    2 * (16384 * H + 5 + 1) ≤ H ^ 2 := by nlinarith only [hH]

 theorem scheduledSeedFactor_bounds (N pass : ℕ) :
    1 ≤ scheduledSeedFactor N pass ∧
      scheduledSeedFactor N pass ≤ ((integerParameters N).initialFactor : ℚ) := by
  constructor
  · exact one_le_pow₀ (by norm_num)
  · rw [← computedSeed_initial_factor]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.sub_le _ _)









noncomputable def computedFamilyTree (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) : DependencyExpansion :=
  physicalFamilyDependencyTree source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2
    (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))

 theorem computedFamilyTree_valid (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (input : ComputedFamilyInput source target N) :
    (computedFamilyTree source target N input).Valid
      ((integerParameters N).M * inputSmallLog N ^ 257)
      (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) :=
  physicalFamilyDependencyTree_valid source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) _ _ _ _
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2 hN hell rfl rfl rfl rfl le_rfl
    (fun p => (scheduledSeedFactor_bounds N p).1) (fun p => (scheduledSeedFactor_bounds N p).2) _

 theorem computedFamilyTree_depth (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    (computedFamilyTree source target N input).depth =
      intervalTreeDepth (integerParameters N).M source.length := by
  unfold computedFamilyTree
  rw [physicalFamilyDependencyTree_depth]
  rfl

 theorem computedFamilyTree_rank (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    (computedFamilyTree source target N input).rank ≤ computedDependencyIndexCount N := by
  unfold computedFamilyTree
  exact physicalFamilyDependencyTree_rank source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) _ _ _ _
    (clampedSeedNat input.1) (computedParameterP_pos N) input.2 rfl rfl rfl _

 theorem computedFamilyTree_width_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hH : 105 ≤ inputHeight N)
    (hsize : source.length + target.length ≤ N) (input : ComputedFamilyInput source target N) :
    ((computedFamilyTree source target N input).widthWork (integerParameters N).M source.length : ℝ) ≤
      computedWidthEnvelope N :=
  computed_widthWork_le_envelope N source.length hN (by omega) hell hH _
    (computedFamilyTree_valid source target N hN hell input)
    (computedFamilyTree_depth source target N input) (computedFamilyTree_rank source target N input)

 theorem computedFamilyResult_requests_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N) (input : ComputedFamilyInput source target N) :
    ((computedFamilyResult source target N input).requests : ℝ) ≤
      ((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N := by
  have hsmall : 200 ≤ inputSmallLog N := two_hundred_le_two_pow_thousand.trans hell
  have hH : 105 ≤ inputHeight N := (by omega : 105 ≤ inputSmallLog N).trans
    (computed_smallLog_le_height N)
  have hr : (computedFamilyResult source target N input).requests ≤
      (inputHeight N ^ 91 + 1) *
        (computedFamilyTree source target N input).widthWork (integerParameters N).M source.length := by
    exact physicalFamilyMemo_requests_le_width source target N (integerParameters N).P
      (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
      (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N) _ _ _ _
      (clampedSeedNat input.1) (computedParameterP_pos N) input.2 hN hsmall rfl
      (fun p => (scheduledSeedFactor_bounds N p).2) (16384 * inputHeight N + 5)
      (computedFamilyMemoCode source target N (inputHeight N ^ 2))
      (computedFamilyMemoCode_injective source target N (inputHeight N ^ 2) hN hsmall)
      (computedFamilyMemoCode_fits source target N (inputHeight N ^ 2) hN hell hsize le_rfl hB) _
  have hrR : ((computedFamilyResult source target N input).requests : ℝ) ≤
      ((inputHeight N : ℝ) ^ 91 + 1) *
        (computedFamilyTree source target N input).widthWork (integerParameters N).M source.length := by
    exact_mod_cast hr
  exact hrR.trans (mul_le_mul_of_nonneg_left
    (computedFamilyTree_width_le source target N hN hsmall hH hsize input) (by positivity))


 theorem computedFamilyResult_requests_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).requests : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 92 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word] with N hw hN hell hB
  intro source target hsize input
  have hH : (2 : ℝ) ≤ inputHeight N := by
    exact_mod_cast (show 2 ≤ inputHeight N from
      ((by decide : 2 ≤ 200).trans two_hundred_le_two_pow_thousand).trans (hell.trans (computed_smallLog_le_height N)))
  have hp : (inputHeight N : ℝ) ^ 91 + 1 ≤ (inputHeight N : ℝ) ^ 92 := by
    exact power_succ_add_one (inputHeight N) hH 91
  calc
    _ ≤ ((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N :=
      computedFamilyResult_requests_le source target N (by omega) hell hsize hB input
    _ ≤ (inputHeight N : ℝ) ^ 92 * computedWidthEnvelope N :=
      mul_le_mul_of_nonneg_right hp (computedWidthEnvelope_nonneg N)
    _ ≤ _ := by simpa only [mul_comm] using hw



 theorem computedFamilyRejectionWork_expected_le (source target : List ℕ) (N : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (seed : ClampedPhysicalSeed (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M source.length) target.length N) :
    (∫ execution, computedFamilyRejectionWork source target N (seed, execution)
      ∂rejectionRuntimeArrayLaw (physicalFamilyRange (M := (integerParameters N).M)
        (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
        target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))) ≤
      2 * ((((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N) * inputHeight N) := by
  apply physicalFamilyMemoBits_expected_le source target N (integerParameters N).P
    (integerParameters N).T (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (inputHeight N)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) (finalTargetState target.length) seed
  · intro draw
    exact computedFamilyResult_requests_le source target N hN hell hsize hB (seed, draw)
  · exact computedFamilyRange_bits_le source target N (inputHeight N ^ 2) hB


 theorem computedFamilyRejectionWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ seed : ComputedFamilySeed source target N,
      (∫ execution, computedFamilyRejectionWork source target N (seed, execution)
        ∂rejectionRuntimeArrayLaw (physicalFamilyRange (M := (integerParameters N).M)
          (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
          target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
          (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 94 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word] with N hw hN hell hB
  intro source target hsize seed
  have hH : (2 : ℝ) ≤ inputHeight N := by
    exact_mod_cast (show 2 ≤ inputHeight N from
      ((by decide : 2 ≤ 200).trans two_hundred_le_two_pow_thousand).trans (hell.trans (computed_smallLog_le_height N)))
  have hfactor : 2 * ((inputHeight N : ℝ) ^ 91 + 1) * inputHeight N ≤
      (inputHeight N : ℝ) ^ 94 := rejection_factor_le (inputHeight N) hH 91
  calc
    _ ≤ 2 * ((((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N) * inputHeight N) :=
      computedFamilyRejectionWork_expected_le source target N (by omega) hell hsize hB seed
    _ = computedWidthEnvelope N * (2 * ((inputHeight N : ℝ) ^ 91 + 1) * inputHeight N) := by ring
    _ ≤ computedWidthEnvelope N * (inputHeight N : ℝ) ^ 94 :=
      mul_le_mul_of_nonneg_left hfactor (computedWidthEnvelope_nonneg N)
    _ ≤ _ := hw


 theorem computedFamilyResult_dictionary_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).dictionaryVisits : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 94 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    inputHeight_real_tendsto.eventually (eventually_ge_atTop 32780),
    computed_localOnlineMassBound_word] with N hw hN hell hH hB
  intro source target hsize input
  have hd : (computedFamilyResult source target N input).dictionaryVisits ≤
      (computedFamilyResult source target N input).requests *
        (2 * (16384 * inputHeight N + 5 + 1)) :=
    (rankedMemoEvaluate_resource_bounds _ _ _ _ _ _).2.1
  have hc : (2 * (16384 * inputHeight N + 5 + 1) : ℕ) ≤ inputHeight N ^ 2 := by
    have hnat : 32780 ≤ inputHeight N := by exact_mod_cast hH
    exact dictionary_factor_le (inputHeight N) hnat
  have hcR : ((2 * (16384 * inputHeight N + 5 + 1) : ℕ) : ℝ) ≤
      (inputHeight N : ℝ) ^ 2 := by exact_mod_cast hc
  have hr := computedFamilyResult_requests_le source target N (by omega) hell hsize hB input
  have hpower : (inputHeight N : ℝ) ^ 91 + 1 ≤ (inputHeight N : ℝ) ^ 92 := by
    exact power_succ_add_one (inputHeight N) (by linarith only [hH]) 91
  have hdR : ((computedFamilyResult source target N input).dictionaryVisits : ℝ) ≤
      ((computedFamilyResult source target N input).requests : ℝ) *
        ((2 * (16384 * inputHeight N + 5 + 1) : ℕ) : ℝ) := by exact_mod_cast hd
  calc
    _ ≤ (((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N) *
        (inputHeight N : ℝ) ^ 2 := hdR.trans (mul_le_mul hr hcR (by positivity)
          (mul_nonneg (by positivity) (computedWidthEnvelope_nonneg N)))
    _ ≤ ((inputHeight N : ℝ) ^ 92 * computedWidthEnvelope N) * (inputHeight N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower
        (computedWidthEnvelope_nonneg N)) (by positivity)
    _ = computedWidthEnvelope N * (inputHeight N : ℝ) ^ 94 := by
      rw [show (94 : ℕ) = 92 + 2 from rfl, pow_add]
      ring
    _ ≤ _ := hw

end EditApproximation

end OAI
