import OAI.Computability.PerfectCompleteness.Decoding.ChildBlockProjection
import OAI.Computability.PerfectCompleteness.Foundations.OriginalPrefixContinuation
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas

namespace OAI

section

namespace PerfectCompleteness.ProjectedPrefixComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem variation_triangle {Ω : Type*} [Fintype Ω]
    (P U Q : FiniteDistribution Ω) :
    P.totalVariation Q ≤ P.totalVariation U + U.totalVariation Q := by
  unfold FiniteDistribution.totalVariation
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => abs_sub_le (P.weight x) (U.weight x) (Q.weight x))
  rw [Finset.sum_add_distrib] at h
  linarith

variable {branch : Nat → Nat} {n k t : Nat}
  {K : Type*} [Fintype K]
  {Z : Fin (branch n) → Type*} [∀ i, Fintype (Z i)]

def assembledLaw (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s j, MixedSupport.Projection (childSlots slots i s j) (projected i z s j))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (CutChildGrouping.Assembled (C := Fin calls) slots rows) :=
  (SparseReplacement.law
    (fun i => FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots i)))
    (ChildBlockProjection.replacementLaws calls rows (fun i => childSlots slots i)
      projected p choiceLaw) β hβ hβ').pushforward (CutChildGrouping.assemble slots rows)

theorem uniform_variation (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s j, MixedSupport.Projection (childSlots slots i s j) (projected i z s j))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (hbranch : 0 < branch n) :
    (assembledLaw calls rows slots projected p choiceLaw β hβ hβ').totalVariation
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^
        branch n - 1) / 2 := by
  let : Nonempty (Fin (branch n)) := ⟨⟨0, hbranch⟩⟩
  have huniform := CutChildGrouping.assemble_law (C := Fin calls) slots rows
  change (FiniteProduct.law (fun i : Fin (branch n) =>
    FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots i)))).pushforward (CutChildGrouping.assemble slots rows) = _ at huniform
  have h := ChildBlockProjection.observed_variation calls rows
    (fun i => childSlots slots i) projected p choiceLaw β hβ hβ'
    (CutChildGrouping.assemble slots rows)
  simpa only [assembledLaw, huniform, Fintype.card_fin] using h

theorem original_variation (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s j, MixedSupport.Projection (childSlots slots i s j) (projected i z s j))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    (assembledLaw calls rows slots projected p choiceLaw β hβ hβ').totalVariation
      (OriginalPrefixContinuation.assembledLaw calls rows repeats slots ν q hbranch) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^
        branch n - 1) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 / branch n) / 2 := by
  have hs := uniform_variation calls rows slots projected p choiceLaw β hβ hβ' hbranch
  have ho := OriginalPrefixContinuation.assembledLaw_variation
    calls rows repeats slots ν q hbranch
  rw [FiniteDistribution.totalVariation_comm] at ho
  exact (variation_triangle _
    (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)) _).trans
      (add_le_add hs ho)

theorem observed_original_variation {E Γ : Type*} [Fintype E] [Fintype Γ]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s j, MixedSupport.Projection (childSlots slots i s j) (projected i z s j))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n)
    (exterior : FiniteDistribution E)
    (observe : E × CutChildGrouping.Assembled (C := Fin calls) slots rows → Γ) :
    ((exterior.product (assembledLaw calls rows slots projected p choiceLaw β hβ hβ')).pushforward observe).totalVariation
      ((exterior.product (OriginalPrefixContinuation.assembledLaw calls rows repeats slots ν q hbranch)).pushforward observe) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^
        branch n - 1) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 / branch n) / 2 :=
  CommonProductVariation.observed_product_le_of_bound exterior _ _ observe
    (original_variation calls rows repeats slots projected p choiceLaw β hβ hβ' ν q hbranch)

end
end PerfectCompleteness.ProjectedPrefixComparison

end

end OAI
