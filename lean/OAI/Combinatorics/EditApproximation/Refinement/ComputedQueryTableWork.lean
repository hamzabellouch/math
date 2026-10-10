import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryRegisters
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryConstants
import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryTableBudget
import OAI.Combinatorics.EditApproximation.Queries.QueryTableSemanticCost

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] queryChargedFamilyTable localRequestValue

abbrev ComputedQueryTableParent (source target : List ℕ) (N : ℕ) :=
  {r : PhysicalTableRequest (integerParameters N).M
    (intervalTreeDepth (integerParameters N).M source.length) target.length //
    r.Bounded (computedSeedPassCount N + 1) (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S}

abbrev ComputedQueryTableKey (source target : List ℕ) (N : ℕ)
    (parent : ComputedQueryTableParent source target N) :=
  ChargedFamilyQueryKey (R := inputHeight N ^ 2) target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) (.inr parent)

def computedQueryTableProgram (source target : List ℕ) (N : ℕ)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (parent : ComputedQueryTableParent source target N) :=
  queryChargedFamilyTable (R := inputHeight N ^ 2) source target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1) (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits parent

/-- Complete dispatcher cost on any oracle storing the proved semantic values. -/
theorem computedQueryTable_work_width :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      ∀ (parent : ComputedQueryTableParent source target N)
      (oracle : ComputedQueryTableKey source target N parent → BinaryFraction),
      (∀ key, (oracle key).width ≤ inputHeight N ^ 3) →
      (∀ child, (oracle (Sum.inr child)).value = computedFamilyTableValue source target N input child.val) →
      (computedQueryTableProgram source target N occurrence symbolBits positionBits parent).work
        oracle (fun _ => 1) ≤ computedLocalKernelBudget computedTableQueryDegree N ∧
      ((computedQueryTableProgram source target N occurrence symbolBits positionBits parent).value oracle).width ≤
        localWarmupWordBudget (integerParameters N).M (inputHeight N ^ 8) +
          preparedKernelWordBudget (integerParameters N).M (inputHeight N ^ 8) := by
  filter_upwards [computedQueryParameters_numeric, computedTableQueryBudget_cap, computedQueryMass_word,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000))]
    with N hnumeric hbudget hmass hN hell
  intro source target hsize input occurrence symbolBits positionBits hsymbol hposition parent oracle hwidth hvalue
  have hsmall : 200 ≤ inputSmallLog N := two_hundred_le_two_pow_thousand.trans hell
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    have h := computed_tree_depth_bound N source.length hN (by omega) hsmall
    nlinarith only [h, hsmall]
  have hregs := computedQueryRegisters N target.length _ hN hell (by omega) hJ parent.val parent.property
  have hhist := computed_history_budget_le_height_sq N (by omega)
  have ht : parent.val.index - (integerParameters N).T - 1 ≤ inputHeight N ^ 2 :=
    (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (parent.property.2.2.trans (by omega)))
  have hnum := hnumeric source.length target.length hsize _ ht parent.val.pass
  have hv := computedQueryParameters_values N 0 hf (Nat.zero_le _)
  have hdelta : 0 ≤ (computedQueryParameters N 0).delta.value := by
    rw [hv.2.2.2.2]
    change 0 ≤ 1 / (inputSmallLog N : ℚ) ^ 10
    positivity
  have h38 : inputHeight N ^ 3 ≤ inputHeight N ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hA := scheduledSeedWordWithWork_range N parent.val.pass
  have hAw := (scheduledSeedWordWithWork_bounds N parent.val.pass hN (by omega) hH).1.trans h38
  have hPd : ∃ j : ℕ, (integerParameters N).P = 2 ^ j := by
    refine ⟨heightExponent N * (coarseExponent (inputSmallLog N) + 20), ?_⟩
    change (2 ^ heightExponent N) ^ (coarseExponent (inputSmallLog N) + 20) = _
    rw [← pow_mul]
  let group := physicalFamilyGroup target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (computedSeedPassCount N) (inputHeight N ^ 2) input.2
  let integer := physicalFamilyInteger source target N (integerParameters N).P (inputSmallLog N)
    (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N) (rationalParameters (inputSmallLog N)).tau
    (rationalParameters (inputSmallLog N)).eta (rationalParameters (inputSmallLog N)).kappa
    (rationalParameters (inputSmallLog N)).delta (computedParameterP_pos N) input.2 (clampedSeedNat input.1)
  have hread (child : {r : ComputedQueryTableParent source target N //
      r.val.combinedRank (integerParameters N).T (integerParameters N).S <
        parent.val.combinedRank (integerParameters N).T (integerParameters N).S}) :
      (oracle (Sum.inr ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)).value =
      localRequestValue source target N (integerParameters N).P (inputSmallLog N)
        (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
        (integerParameters N).T (integerParameters N).S (inputHeight N ^ 2)
        (scheduledSeedFactor N) (scheduledSeedMultiplier N) (computedQueryParameters N 0).tau.value
        (computedQueryParameters N 0).eta.value (computedQueryParameters N 0).kappa.value
        (computedQueryParameters N 0).delta.value group integer (clampedSeedNat input.1) child.val.val := by
    rw [hvalue]
    simp only [computedFamilyTableValue, physicalFamilyRequestValue, chargedRequestValue,
      hv.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2]
    rfl
  have hc := queryChargedFamilyTable_semantic_work_bound source target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (integerParameters N).initialFactor
    (inputHeight N ^ 8) (inputHeight N ^ 5)
    (inputHeight N ^ ((100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)))
    (inputHeight N ^ 3) 1 (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1) (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits parent oracle (fun _ => 1)
    (scheduledSeedFactor N) group integer (clampedSeedNat input.1)
    hnum hPd (by exact (by omega : 2 ≤ inputHeight N).trans (Nat.le_pow (by decide))) h38 hregs.mean
    hregs.targetSuccessor hregs.initial hregs.depth hregs.index hregs.warmup hregs.refinement hregs.rank
    hAw hA.1 hA.2 hregs.pass hregs.copy hregs.passes hregs.copies hregs.multiplier
    (hmass.trans (Nat.le_pow (by decide))) (fun key => hwidth _) (fun key => (hwidth _).trans h38)
    (fun _ => le_rfl) hdelta hread
  have hw := queryChargedFamilyTable_semantic_width source target N (integerParameters N).P
    (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (inputHeight N ^ 8)
    (inputHeight N ^ 5)
    (inputHeight N ^ ((100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)))
    (computedParameterP_pos N) rfl rfl
    (fun pass => (scheduledSeedWordWithWork N pass).1) (fun pass => (computedQueryParameters N pass).factor)
    (computedQueryParameters N 0).tau (computedQueryParameters N 0).eta
    (computedQueryParameters N 0).kappa (computedQueryParameters N 0).delta
    (scheduledSeedMultiplier N) occurrence symbolBits positionBits parent oracle
    (scheduledSeedFactor N) group integer (clampedSeedNat input.1) hnum hregs.targetSuccessor hregs.initial
    hregs.index (fun key => (hwidth _).trans h38) hdelta hread
  refine ⟨?_, hw⟩
  apply hc.trans
  convert hbudget (integerParameters N).initialFactor _ symbolBits positionBits
    (parent.val.index - (integerParameters N).T) (computedQueryInitialFactor_cap N) hJ hsymbol hposition
    ((Nat.sub_le _ _).trans (parent.property.2.2.trans (by omega))) using 1
  rfl

end EditApproximation

end OAI
