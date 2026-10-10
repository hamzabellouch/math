import OAI.Computability.PerfectCompleteness.Construction.OriginalChildScalarAssemblyLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CommonAccuracy
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutCallsLemmas

namespace OAI


namespace PerfectCompleteness.FixedCallBudget

open RecursiveSpaces DescendantSpaces
open scoped BigOperators

noncomputable section

def pairCount (rows repeats : Nat → Nat) (root cutoff : Nat) : Nat :=
  rows cutoff + OriginalCutCalls.count rows repeats root cutoff

def budget (depth : Nat) (rows repeats : Nat → Nat) : Nat :=
  1 + ∑ root : Fin (depth + 1), ∑ cutoff : Fin (depth + 1),
    pairCount rows repeats root.val cutoff.val

theorem budget_pos (depth : Nat) (rows repeats : Nat → Nat) :
    0 < budget depth rows repeats := by
  unfold budget
  omega

theorem pairCount_le {depth root cutoff : Nat} (rows repeats : Nat → Nat)
    (hroot : root ≤ depth) (hcutoff : cutoff ≤ depth) :
    pairCount rows repeats root cutoff ≤ budget depth rows repeats := by
  let a : Fin (depth + 1) := ⟨root, Nat.lt_succ_of_le hroot⟩
  let b : Fin (depth + 1) := ⟨cutoff, Nat.lt_succ_of_le hcutoff⟩
  have hinner : pairCount rows repeats root cutoff ≤
      ∑ j : Fin (depth + 1), pairCount rows repeats a.val j.val :=
    Finset.single_le_sum (fun j _ => Nat.zero_le
      (pairCount rows repeats a.val j.val)) (Finset.mem_univ b)
  have houter : (∑ j : Fin (depth + 1), pairCount rows repeats a.val j.val) ≤
      ∑ i : Fin (depth + 1), ∑ j : Fin (depth + 1),
        pairCount rows repeats i.val j.val :=
    Finset.single_le_sum (fun i _ => Nat.zero_le
      (∑ j : Fin (depth + 1), pairCount rows repeats i.val j.val))
      (Finset.mem_univ a)
  unfold budget
  omega

theorem original_calls_le {depth root cutoff : Nat} {branch : Nat → Nat}
    (rows repeats : Nat → Nat) (p : Path branch root cutoff)
    (hroot : root ≤ depth) :
    Fintype.card (OriginalCutCalls.Index rows repeats p) ≤ budget depth rows repeats := by
  rw [OriginalCutCalls.card_eq_count]
  have h := pairCount_le rows repeats hroot (p.height_le.trans hroot)
  unfold pairCount at h
  omega

theorem modified_calls_le {depth root cutoff : Nat} {branch : Nat → Nat}
    (rows repeats : Nat → Nat) (p : Path branch root cutoff)
    (hroot : root ≤ depth) :
    Fintype.card (WholeCutCalls.Index rows repeats p) ≤ budget depth rows repeats := by
  rw [WholeCutCalls.card_eq_formula]
  have h := pairCount_le rows repeats hroot (p.height_le.trans hroot)
  unfold pairCount OriginalCutCalls.count at h
  omega

theorem copied_calls_le {calls copies depth : Nat} (rows repeats : Nat → Nat)
    (hcalls : calls ≤ budget depth rows repeats) :
    Fintype.card (Fin copies × Fin calls) ≤ copies * budget depth rows repeats := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    Nat.mul_le_mul_left copies hcalls

theorem child_bound_mono {calls calls' : Nat} (hcalls : calls ≤ calls')
    (branch : Nat → Nat) (height sourceLength : Nat) (rows : Nat → Nat) :
    ChildBlockCardinality.bound branch height sourceLength calls rows ≤
      ChildBlockCardinality.bound branch height sourceLength calls' rows := by
  apply Nat.mul_le_mul_right
  apply pow_le_pow_right₀ _ hcalls
  unfold TreeCardinality.functionBound
  exact one_le_pow₀ (by decide : (1 : Nat) ≤ 2)

theorem copied_calls_with_extra_le {calls copies extra depth : Nat}
    (rows repeats : Nat → Nat) (hcalls : calls ≤ budget depth rows repeats) :
    Fintype.card ((Fin copies × Fin calls) ⊕ Fin extra) ≤
      copies * budget depth rows repeats + extra := by
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using
    Nat.add_le_add_right (Nat.mul_le_mul_left copies hcalls) extra

end
end PerfectCompleteness.FixedCallBudget


namespace PerfectCompleteness.FixedParameters

open FixedRows AscendingBranching

noncomputable section

def calls {δ : ℚ} (plan : Plan δ) : Nat :=
  2 * FixedCallBudget.budget plan.depth (rows plan) (repeats plan) + 1

structure Parameters (δ : ℚ) (positive : 0 < δ) where
  plan : Plan δ
  accuracy : ℝ
  accuracy_pos : 0 < accuracy
  accuracy_small : ∀ j ≤ plan.depth, accuracy < CommonAccuracy.tolerance plan j
  alphabetCost : Nat
  alphabetCost_pos : 0 < alphabetCost
  alphabetCost_bound : SourceOddLists.alphabetLog (cutoff plan positive)
    (sourceLength plan positive) ≤ alphabetCost
  cubeSize : Nat → Nat
  cube_errors : ∀ n,
    CubeErrors
      (ChildBlockCardinality.bound (fun k => cubeSize k ^ 3) n
        (sourceLength plan positive) (calls plan) (rows plan) : ℝ)
      (FixedBranching.cleanRate alphabetCost
        (ChildBlockCardinality.bound (fun k => cubeSize k ^ 3) n
          (sourceLength plan positive) (calls plan) (rows plan) : ℝ))
      accuracy (cubeSize n)

theorem exists_parameters {δ : ℚ} (hδ : 0 < δ) (hδ' : δ < 1) :
    Nonempty (Parameters δ hδ) := by
  obtain ⟨plan⟩ := exists_plan hδ hδ'
  obtain ⟨accuracy, haccuracy, hsmall⟩ := CommonAccuracy.exists_accuracy plan hδ
  obtain ⟨cost, hcost, hcostBound, size, hsize⟩ :=
    FixedSourceBranching.exists_source_branching plan hδ
      (fun _ => calls plan) haccuracy
  refine ⟨{
    plan := plan
    accuracy := accuracy
    accuracy_pos := haccuracy
    accuracy_small := ?_
    alphabetCost := cost
    alphabetCost_pos := hcost
    alphabetCost_bound := hcostBound
    cubeSize := size
    cube_errors := hsize }⟩
  intro j hj
  simpa only [CommonAccuracy.tolerance, lt_min_iff] using hsmall j hj

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

def branch (n : Nat) : Nat := p.cubeSize n ^ 3
def projectionProbability (n : Nat) : ℚ := 1 / (p.cubeSize n : ℚ) ^ 2

theorem branch_pos (n : Nat) : 0 < branch p n := by
  have h := (p.cube_errors n).1
  unfold branch
  positivity

theorem projectionProbability_bounds (n : Nat) :
    0 < projectionProbability p n ∧ projectionProbability p n < 1 :=
  FixedBranching.rational_probability (p.cube_errors n).1

theorem source_rate (input : List Bool) (unsat : ¬BinaryLanguage.language input)
    (k : Nat) :
    ((SourceOddLists.game (cutoff p.plan hδ)
      (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      (sourceLength p.plan hδ)).repetition k).value ≤
      (RepetitionRate.halfRate p.alphabetCost : ℝ) ^ k :=
  FixedSourceBranching.source_rate p.plan hδ p.alphabetCost
    p.alphabetCost_pos p.alphabetCost_bound input unsat k

end
end PerfectCompleteness.FixedParameters

end OAI
