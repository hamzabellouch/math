import OAI.Computability.PerfectCompleteness.Decoding.OriginalWholeCutProjection
import OAI.Computability.PerfectCompleteness.Decoding.UpperCutOldRecord
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedCutChoices

namespace OAI

section

namespace PerfectCompleteness.ProjectedWholeCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem product_mixture {E A B Γ : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype Γ]
    (μ : FiniteDistribution E) (ν : FiniteDistribution A)
    (P : A → FiniteDistribution B) (f : E × B → Γ) :
    (μ.product (ν.mixture P)).pushforward f =
      ν.mixture (fun a => (μ.product (P a)).pushforward f) := by
  have hproduct : μ.product (ν.mixture P) = ν.mixture (fun a => μ.product (P a)) := by
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    change μ.weight x.1 * (∑ a, ν.weight a * (P a).weight x.2) =
      ∑ a, ν.weight a * (μ.weight x.1 * (P a).weight x.2)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hproduct, FiniteDistribution.pushforward_mixture]

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

variable {branch : Nat → Nat} {n m j t : Nat}
  (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  {Z : Fin (branch m) → Type*} [∀ child, Fintype (Z child)]
  (projected : (child : Fin (branch m)) → Z child → Slots branch m → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots (cutSlots p slots) child s a) (projected child z s a))

def fullSlots (choices : ProjectedCutChoices.Choices (Z := Z)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p slots
    (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)

theorem fill_native : CutSlotAssembly.fill p slots (cutSlots p slots) = slots :=
  CutSlotAssembly.fill_restrict p slots

def fullProjection (choices : ProjectedCutChoices.Choices (Z := Z)) :
    ∀ s a, MixedSupport.Projection (slots s a) (fullSlots p slots projected choices s a) :=
  fun s a => CutProjectionAssembly.castProjection
    (congrFun (congrFun (fill_native p slots) s) a) rfl
    (CutProjectionAssembly.fillProjection p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices) s a)

omit [∀ child, Fintype (Z child)] in
theorem cut_fullSlots (choices : ProjectedCutChoices.Choices (Z := Z)) :
    cutSlots p (fullSlots p slots projected choices) =
      ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices := by
  funext s a
  exact congrFun (CutSlotAssembly.fill_at_cut p slots
    (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices) s) a

omit [∀ child, Fintype (Z child)] in
theorem cut_fullProjection (choices : ProjectedCutChoices.Choices (Z := Z))
    (s : Slots branch (m + 1)) (a : Fin t) :
    HEq (CutGroupedProjection.cutProjection p (fullProjection p slots projected projection choices) s a)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices s a) :=
  (CutProjectionAssembly.castProjection_heq
    (congrFun (congrFun (fill_native p slots) (p.slotEmbedding s)) a) rfl
    (CutProjectionAssembly.fillProjection p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices)
      (p.slotEmbedding s) a)).trans
    (CutProjectionAssembly.fillProjection_at_cut p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices) s a)

omit [∀ child, Fintype (Z child)] in
theorem fullSlots_outside (choices : ProjectedCutChoices.Choices (Z := Z))
    (s : Slots branch n) (hs : WholeCutExteriorTransport.Outside p s) :
    slots s = fullSlots p slots projected choices s := by
  calc
    slots s = CutSlotAssembly.fill p slots (cutSlots p slots) s :=
      (congrFun (fill_native p slots) s).symm
    _ = _ := CutSlotAssembly.fill_outside_eq p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices) s hs

omit [∀ child, Fintype (Z child)] in
theorem fullProjection_outside (choices : ProjectedCutChoices.Choices (Z := Z))
    (s : Slots branch n) (hs : WholeCutExteriorTransport.Outside p s) (a : Fin t) :
    HEq (fullProjection p slots projected projection choices s a)
      (MixedSupport.Projection.keep (slots s a)) := by
  have hkeep : HEq
      (MixedSupport.Projection.keep (CutSlotAssembly.fill p slots (cutSlots p slots) s a))
      (MixedSupport.Projection.keep (slots s a)) := by
    rw [fill_native p slots]
  exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
    ((CutProjectionGeometry.fillProjection_outside p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices) s hs a).trans
        hkeep)

omit [∀ child, Fintype (Z child)] in
theorem fixed_law (rows repeats : Nat → Nat) (choices : ProjectedCutChoices.Choices (Z := Z)) :
    ((OriginalWholeCutTape.exteriorLaw rows repeats p slots).product
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1)))
        (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows
            (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices)))).pushforward
              (OriginalWholeCutBridge.reconstruct rows repeats p slots) =
      (WholeArraySampler.law rows repeats p (fullSlots p slots projected choices)).pushforward
        (ChildBlockProjection.arraysPullback rows (fullProjection p slots projected projection choices)) := by
  have h := OriginalWholeCutProjection.fixed_projected_law rows repeats p slots
    (fullSlots p slots projected choices) (fullProjection p slots projected projection choices)
    (fullSlots_outside p slots projected choices)
    (fullProjection_outside p slots projected projection choices)
  have hblocks := lifted_assembled_congr (OriginalCutCalls.count rows repeats n (m + 1)) rows
    (cutSlots p slots) (cutSlots p (fullSlots p slots projected choices))
    (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
    (CutGroupedProjection.cutProjection p (fullProjection p slots projected projection choices))
    (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices)
    (cut_fullSlots p slots projected choices)
    (cut_fullProjection p slots projected projection choices)
  rw [hblocks] at h
  exact h

def arrayLaw (rows repeats : Nat → Nat)
    (choiceLaw : (child : Fin (branch m)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) : FiniteDistribution (Arrays slots rows) :=
  (ProjectedCutChoices.choicesLaw choiceLaw β hβ hβ').mixture (fun choices =>
    (WholeArraySampler.law rows repeats p (fullSlots p slots projected choices)).pushforward
      (ChildBlockProjection.arraysPullback rows (fullProjection p slots projected projection choices)))

theorem reconstruct_assembled_law (rows repeats : Nat → Nat)
    (choiceLaw : (child : Fin (branch m)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((OriginalWholeCutTape.exteriorLaw rows repeats p slots).product
      (ProjectedPrefixComparison.assembledLaw (OriginalCutCalls.count rows repeats n (m + 1))
        rows (cutSlots p slots) projected projection choiceLaw β hβ hβ')).pushforward
          (OriginalWholeCutBridge.reconstruct rows repeats p slots) =
      arrayLaw p slots projected projection rows repeats choiceLaw β hβ hβ' := by
  rw [ProjectedCutChoices.assembled_eq_mixture (cutSlots p slots) projected projection
    (OriginalCutCalls.count rows repeats n (m + 1)) rows choiceLaw β hβ hβ', product_mixture]
  unfold arrayLaw
  apply congrArg ((ProjectedCutChoices.choicesLaw choiceLaw β hβ hβ').mixture)
  funext choices
  exact fixed_law p slots projected projection rows repeats choices

theorem old_arrayLaw_eq (rows repeats : Nat → Nat) (upperPath : Path branch n (j + 1))
    (lowerPath : Path branch (j + 1) (m + 1))
    (projected : (child : Fin (branch m)) → Z child → Slots branch m → Fin t → MixedSupport.Slot)
    (projection : ∀ child z s a, MixedSupport.Projection
      (childSlots (cutSlots (upperPath.append lowerPath) slots) child s a) (projected child z s a))
    (choiceLaw : (child : Fin (branch m)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UpperCutOldRecord.arrayLaw rows repeats upperPath lowerPath slots
      projected projection choiceLaw β hβ hβ' =
    arrayLaw (upperPath.append lowerPath) slots projected projection rows repeats choiceLaw β hβ hβ' :=
  reconstruct_assembled_law (upperPath.append lowerPath) slots projected projection
    rows repeats choiceLaw β hβ hβ'

end
end PerfectCompleteness.ProjectedWholeCut

end

end OAI
