import OAI.Combinatorics.EditApproximation.Binary.BitMemoHeap
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryHeap
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryStorage
import OAI.Combinatorics.EditApproximation.Refinement.ComputedBaseStorage
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryWork
import OAI.Combinatorics.EditApproximation.Geometry.MemoCodeWork

namespace OAI

namespace EditApproximation
open Filter
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- Cumulative concrete local allocations, address workspace, suspended
reads, dictionary paths and evaluator frames, over the actual cache trace. -/
def computedQueryTemporaryCells (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) : ℕ :=
  rankedBitMemoCells (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (computedQueryMemoHeap source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (fun key => (computedFamilyMemoCodeWithWork source target N (inputHeight N ^ 2) key).2)
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty

theorem computedQueryTemporaryCells_bound (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (input : ComputedFamilyInput source target N) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) (hf : 3 ≤ smallLogExponent N)
    (hsize : source.length + target.length ≤ N)
    (hMass : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx) :
    computedQueryTemporaryCells source target N occurrence symbolBits positionBits input ≤
      3 * computedFamilyKernelWork source target N input
          (computedQueryLocalWork source target N occurrence symbolBits positionBits input) +
        (memoRequestCells (16384 * inputHeight N + 5)
          (7 * intervalTreeDepth (integerParameters N).M source.length + 60) + 3) *
          (computedFamilyResult source target N input).requests := by
  have h := rankedBitMemoCells_le (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoNormalized source target N occurrence symbolBits positionBits input)
    (computedQueryMemoHeap source target N occurrence symbolBits positionBits input)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (fun key => (computedFamilyMemoCodeWithWork source target N (inputHeight N ^ 2) key).2)
    (7 * intervalTreeDepth (integerParameters N).M source.length + 60)
    (computedFamilyMemoCodeWithWork_cost source target N (inputHeight N ^ 2))
    (.inr (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length))) .empty
  change computedQueryTemporaryCells source target N occurrence symbolBits positionBits input + 3 ≤
    3 * (computedQueryMemoResult source target N occurrence symbolBits positionBits input).localWork +
      _ * (computedQueryMemoResult source target N occurrence symbolBits positionBits input).requests at h
  rw [computedQueryMemoResult_localWork source target N occurrence symbolBits positionBits input
    hN hell hf hsize hMass hs ht hp htable] at h
  have hd := congrArg RecursiveMemoResult.requests
    (computedQueryMemoResult_decode source target N occurrence symbolBits positionBits input
      hN hell hf hsize hMass hs ht hp htable)
  change (computedQueryMemoResult source target N occurrence symbolBits positionBits input).requests = _ at hd
  rw [hd] at h
  omega

private theorem requestCells_factor (H J : ℕ) (hH : 100 ≤ H) (hJ : J ≤ H) :
    memoRequestCells (16384 * H + 5) (7 * J + 60) + 3 ≤ H ^ 4 := by
  have hcoef : 200000 ≤ H ^ 3 :=
    (by norm_num : 200000 ≤ (100 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hH 3)
  have hp : 200000 * H ≤ H ^ 4 := (Nat.mul_le_mul_right H hcoef).trans_eq (by ring)
  unfold memoRequestCells
  omega

theorem computedQueryTemporaryCells_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
        (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
      target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
      computedQueryTemporaryCells source target N occurrence symbolBits positionBits input ≤ (N + 2) ^ 20 := by
  filter_upwards [computedQueryLocalWork_cap,
    computedFamilyKernelWork_polynomial computedQueryWorkDegree,
    computedFamilyResult_requests_near_linear 1 (by norm_num), computedQueryMass_word,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))]
    with N hcap hwork hrequests hMass hN hell
  intro source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hl := hwork source target hsize input _
    (hcap source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc)
  have hr : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hrequests source target hsize input
    norm_num at h
    exact_mod_cast h
  have hH : 100 ≤ inputHeight N :=
    (by have := two_hundred_le_two_pow_thousand.trans hell; omega : 100 ≤ inputSmallLog N).trans
      (computed_smallLog_le_height N)
  have hd := computed_tree_depth_bound N source.length hN (by omega)
    (two_hundred_le_two_pow_thousand.trans hell)
  have hhundred : 100 ≤ inputSmallLog N := by
    have := two_hundred_le_two_pow_thousand.trans hell
    omega
  have hm := Nat.mul_le_mul_left (intervalTreeDepth (integerParameters N).M source.length) hhundred
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    nlinarith only [hd, hm]
  have hc := requestCells_factor (inputHeight N) _ hH hJ
  have hpoly : inputHeight N ^ 4 ≤ (N + 2) ^ 16 :=
    (Nat.pow_le_pow_left (computed_height_polynomial N) 4).trans_eq (by rw [← pow_mul])
  have hb := computedQueryTemporaryCells_bound source target N occurrence symbolBits positionBits
    input hN hell hf hsize hMass hs ht hp hoc
  have hprod := Nat.mul_le_mul (hc.trans hpoly) hr
  have h2 : (N + 2) ^ 2 ≤ (N + 2) ^ 18 := Nat.pow_le_pow_right (by omega) (by decide)
  have hfour : 4 * (N + 2) ^ 18 ≤ (N + 2) ^ 20 := by
    calc
      _ ≤ (N + 2) ^ 2 * (N + 2) ^ 18 := Nat.mul_le_mul_right _ (by nlinarith [Nat.zero_le N])
      _ = _ := by rw [← pow_add]
  rw [← pow_add] at hprod
  change _ ≤ (N + 2) ^ 18 at hprod
  omega

end EditApproximation

end OAI
