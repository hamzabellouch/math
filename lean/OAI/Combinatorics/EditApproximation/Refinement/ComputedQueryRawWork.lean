import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryTableWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryNormalizationBudget
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryExecution

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] queryChargedFamilyTable localRequestValue

def computedQueryRawWorkDegree : ℕ := max 1 computedTableQueryDegree
def computedQueryRawWidthDegree : ℕ := max 1 queryRawWordDegree

/-- Every raw body is charged on the actual, proved normalized-child oracle. -/
theorem computedQueryMemoRaw_bounds :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
      target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
      ∀ key : ComputedFamilyMemoKey source target N,
      let oracle := fun child : {child : ComputedFamilyMemoKey source target N //
          SourceRanked.rank ChargedPhysicalRequest.rank child <
            SourceRanked.rank ChargedPhysicalRequest.rank key} => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
        (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) child.val
      (computedQueryMemoRaw source target N occurrence symbolBits positionBits input key).work oracle (fun _ => 0) ≤
        computedLocalKernelBudget computedQueryRawWorkDegree N ∧
      ((computedQueryMemoRaw source target N occurrence symbolBits positionBits input key).value oracle).width ≤
        computedLocalKernelBudget computedQueryRawWidthDegree N := by
  filter_upwards [computedQueryTable_work_width, computedQueryRawWidth_cap, computedQueryMass_word,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))]
    with N htable hraw hmass hN hell
  intro source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc key
  dsimp only
  have hsmall : 200 ≤ inputSmallLog N := two_hundred_le_two_pow_thousand.trans hell
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hg := computed_kernel_guard_cost N hH
  have hsmallBudget : inputHeight N + 3 ≤ computedLocalKernelBudget 1 N := by
    have hpow : inputHeight N ≤ inputHeight N ^ 8 := Nat.le_pow (by decide)
    omega
  have hworkMono := computedLocalKernelBudget_mono N 1 computedQueryRawWorkDegree (Nat.le_max_left _ _)
  have hwidthMono := computedLocalKernelBudget_mono N 1 computedQueryRawWidthDegree (Nat.le_max_left _ _)
  have hrawMono := computedLocalKernelBudget_mono N queryRawWordDegree computedQueryRawWidthDegree
    (Nat.le_max_right _ _)
  have htableMono := computedLocalKernelBudget_mono N computedTableQueryDegree computedQueryRawWorkDegree
    (Nat.le_max_right _ _)
  cases key with
  | inl key =>
    have hr := computedFamilyRange_bits_le source target N (inputHeight N ^ 2) hmass key
    have hc : (input.2 key).val < 2 ^ inputHeight N := (input.2 key).isLt.trans_le
      ((Nat.le_pow_clog (by decide : 1 < 2) _).trans
        (Nat.pow_le_pow_right (by decide : 0 < 2) hr))
    have hb : Nat.size (input.2 key).val ≤ inputHeight N := Nat.size_le.mpr hc
    change Nat.size (input.2 key).val + 3 ≤ _ ∧ (nat (input.2 key).val).width ≤ _
    exact ⟨(by omega : Nat.size (input.2 key).val + 3 ≤ computedLocalKernelBudget 1 N).trans hworkMono,
      (nat_width_le _).trans ((by omega : Nat.size (input.2 key).val + 2 ≤ computedLocalKernelBudget 1 N).trans hwidthMono)⟩
  | inr key =>
    cases key with
    | inl entry =>
      have hb : Nat.size (clampedSeedNat input.1 entry) ≤ inputHeight N :=
        (Nat.size_le_size (Nat.le_of_lt_succ (input.1 entry).isLt)).trans (computed_input_size_le_height N)
      change 0 ≤ _ ∧ (nat (clampedSeedNat input.1 entry)).width ≤ _
      exact ⟨Nat.zero_le _, (nat_width_le _).trans
        ((by omega : Nat.size (clampedSeedNat input.1 entry) + 2 ≤ computedLocalKernelBudget 1 N).trans hwidthMono)⟩
    | inr parent =>
      let oracle := fun child : {child : ComputedFamilyMemoKey source target N //
          SourceRanked.rank ChargedPhysicalRequest.rank child <
            SourceRanked.rank ChargedPhysicalRequest.rank (.inr (.inr parent) : ComputedFamilyMemoKey source target N)} => rankedBitProgramValue (SourceRanked.rank ChargedPhysicalRequest.rank)
        (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input) child.val
      let tableOracle : ComputedQueryTableKey source target N parent → BinaryFraction :=
        fun child => oracle (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child)
      have hw (child) : (tableOracle child).width ≤ inputHeight N ^ 3 :=
        computedQueryMemoNormalized_width source target N occurrence symbolBits positionBits input hN hsmall hf
          hsize hmass hs ht hp hoc _
      have hv (child) : (tableOracle (Sum.inr child)).value = computedFamilyTableValue source target N input child.val :=
        (computedQueryMemoNormalized_correct source target N occurrence symbolBits positionBits input hf hs ht hp hoc _).1
      have hb := htable source target hsize input occurrence symbolBits positionBits hsb hpb parent tableOracle hw hv
      change (BitQuery.mapKeysWithWork (fun child =>
          (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
        (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)).work oracle (fun _ => 0) ≤ _ ∧
        ((BitQuery.mapKeysWithWork (fun child =>
          (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
          (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)).value oracle).width ≤ _
      constructor
      · exact (BitQuery.mapKeysWithWork_work
          (fun child : ComputedQueryTableKey source target N parent =>
            (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
          (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)
          oracle (fun _ => 0)).trans_le (hb.1.trans htableMono)
      · exact (congrArg BinaryFraction.width (BitQuery.mapKeysWithWork_value
          (fun child : ComputedQueryTableKey source target N parent =>
            (SourceRanked.child ChargedPhysicalRequest.rank (.inr parent) child, 1))
          (computedQueryTableProgram source target N occurrence symbolBits positionBits parent)
          oracle)).trans_le (hb.2.trans (hraw.trans hrawMono))

end EditApproximation

end OAI
