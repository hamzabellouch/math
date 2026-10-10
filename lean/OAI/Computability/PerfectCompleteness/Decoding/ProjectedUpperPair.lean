import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutProjection
import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarFreshProjectionLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedWholeCut

namespace OAI

section

namespace PerfectCompleteness.ProjectedUpperPair

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

attribute [local instance] linearMapFintype

private theorem product_mixture_right {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (P : B → FiniteDistribution C) :
    μ.product (ν.mixture P) = ν.mixture (fun b => μ.product (P b)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change μ.weight x.1 * (∑ b, ν.weight b * (P b).weight x.2) =
    ∑ b, ν.weight b * (μ.weight x.1 * (P b).weight x.2)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem lifted_assembled_congr {branch : Nat → Nat} {m t : Nat}
    (calls : Nat) (rows : Nat → Nat)
    (left right right' : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (q' : ∀ s a, MixedSupport.Projection (left s a) (right' s a))
    (hright : right = right') (hq : ∀ s a, HEq (q s a) (q' s a)) :
    (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) right rows)).pushforward
      (ChildAssemblyProjection.assembledPullback rows q) =
    (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) right' rows)).pushforward
      (ChildAssemblyProjection.assembledPullback rows q') := by
  cases hright
  have heq : q = q' := by
    funext s a
    exact eq_of_heq (hq s a)
  cases heq
  rfl

variable {branch : Nat → Nat} {n j i t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

variable (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  {Z : Fin (branch i) → Type*} [∀ child, Fintype (Z child)]
  (projected : (child : Fin (branch i)) → Z child → Slots branch i → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots (cutSlots (p.append r) slots) child s a) (projected child z s a))

omit [∀ child, Fintype (Z child)] in
theorem fixed_law (rows repeats : Nat → Nat) (hproper : i + 1 < j + 1)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (choices : ProjectedCutChoices.Choices (Z := Z)) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
        (ProjectedCutChoices.selectedSlots (cutSlots (p.append r) slots) projected choices) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows
            (ProjectedCutChoices.selectedProjection (cutSlots (p.append r) slots)
              projected projection choices))) =
      (directions.product
        ((WholeArraySampler.tapeLaw rows repeats (p.append r)
          (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)).product
          (RecursiveSampler.law F2 repeats r
            (LeafDomain (cutSlots p
              (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)))))).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper slots
          (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)
          (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices)) := by
  have h := UpperScalarCutProjection.fixed_projected_law rows repeats p r hproper slots
    (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)
    (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices)
    (ProjectedWholeCut.fullSlots_outside (p.append r) slots projected choices)
    (ProjectedWholeCut.fullProjection_outside (p.append r) slots projected projection choices)
    directions
  have hblocks := lifted_assembled_congr
    (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
    (cutSlots (p.append r) slots)
    (cutSlots (p.append r) (ProjectedWholeCut.fullSlots (p.append r) slots projected choices))
    (ProjectedCutChoices.selectedSlots (cutSlots (p.append r) slots) projected choices)
    (CutGroupedProjection.cutProjection (p.append r)
      (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices))
    (ProjectedCutChoices.selectedProjection (cutSlots (p.append r) slots) projected projection choices)
    (ProjectedWholeCut.cut_fullSlots (p.append r) slots projected choices)
    (ProjectedWholeCut.cut_fullProjection (p.append r) slots projected projection choices)
  rw [hblocks] at h
  exact h

def pairLaw (rows repeats : Nat → Nat) (hproper : i + 1 < j + 1)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (choiceLaw : (child : Fin (branch i)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p)) :=
  (ProjectedCutChoices.choicesLaw choiceLaw β hβ hβ').mixture (fun choices =>
    (directions.product
      ((WholeArraySampler.tapeLaw rows repeats (p.append r)
        (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)).product
        (RecursiveSampler.law F2 repeats r
          (LeafDomain (cutSlots p
            (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)))))).pushforward
      (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper slots
        (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)
        (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices)))

theorem reconstruct_assembled_law (rows repeats : Nat → Nat) (hproper : i + 1 < j + 1)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (choiceLaw : (child : Fin (branch i)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      (ProjectedPrefixComparison.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
        (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ') =
      pairLaw p r slots projected projection rows repeats hproper directions choiceLaw β hβ hβ' := by
  unfold UpperScalarPairComparison.pairLaw
  rw [ProjectedCutChoices.assembled_eq_mixture (cutSlots (p.append r) slots) projected projection
    (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows choiceLaw β hβ hβ',
    product_mixture_right, product_mixture_right, FiniteDistribution.pushforward_mixture]
  unfold pairLaw
  apply congrArg ((ProjectedCutChoices.choicesLaw choiceLaw β hβ hβ').mixture)
  funext choices
  exact fixed_law p r slots projected projection rows repeats hproper directions choices

end
end PerfectCompleteness.ProjectedUpperPair

end

end OAI
