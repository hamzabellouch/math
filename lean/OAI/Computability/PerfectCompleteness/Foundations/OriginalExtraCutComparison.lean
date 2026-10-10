import OAI.Computability.PerfectCompleteness.Foundations.ExtraCutCall
import OAI.Computability.PerfectCompleteness.Foundations.OriginalPrefixContinuation
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas

namespace OAI

section

namespace PerfectCompleteness.OriginalExtraCutComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

private theorem product_mixture_pushforward {E A B Γ : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype Γ]
    (μ : FiniteDistribution A) (κ : FiniteDistribution E)
    (ν : E → FiniteDistribution B) (f : A × B → Γ) :
    (μ.product (κ.mixture ν)).pushforward f =
      κ.mixture (fun e => (μ.product (ν e)).pushforward f) := by
  have hp : μ.product (κ.mixture ν) = κ.mixture (fun e => μ.product (ν e)) := by
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    simp only [FiniteDistribution.product, FiniteDistribution.mixture, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact mul_left_comm _ _ _
  rw [hp, FiniteDistribution.pushforward_mixture]

variable {branch : Nat → Nat} {n m k t : Nat} {K : Type*} [Fintype K]

abbrev Record (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalWholeCutBridge.NumberedRecord rows repeats p slots × H (cutSlots p slots)

def actualLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m) :
    FiniteDistribution (Record rows repeats p slots) :=
  ((exteriorLaw rows repeats p slots).product
    (OriginalPrefixContinuation.assembledLaw
      (OriginalCutCalls.count rows repeats n (m + 1) + 1)
      rows repeats (cutSlots p slots) ν q hbranch)).pushforward
        (ExtraCutCall.splitRecord rows repeats p slots)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

def referenceLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Record rows repeats p slots) :=
  ((OriginalUniformCut.referenceLaw rows repeats p slots).pushforward
    (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
      (FiniteDistribution.uniform (H (cutSlots p slots)))

theorem actualLaw_eq_mixture (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m) :
    actualLaw rows repeats p slots ν q hbranch =
      (OriginalPrefixContinuation.tagLaw ν hbranch).mixture (fun tag =>
        ((recordLaw rows repeats p tag.1 (q tag.2) slots).pushforward
          (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
            (RecursiveSampler.law F2 repeats (.step tag.1 (q tag.2))
              (LeafDomain (cutSlots p slots)))) := by
  unfold actualLaw
  rw [OriginalPrefixContinuation.assembledLaw_eq_mixture, product_mixture_pushforward]
  apply congrArg ((OriginalPrefixContinuation.tagLaw ν hbranch).mixture)
  funext tag
  exact ExtraCutCall.record_fresh_law rows repeats p tag.1 (q tag.2) slots

theorem totalVariation_le (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m) :
    (actualLaw rows repeats p slots ν q hbranch).totalVariation
      (referenceLaw rows repeats p slots) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 := by
  unfold actualLaw referenceLaw
  rw [← ExtraCutCall.uniform_record_fresh_law rows repeats p slots]
  exact CommonProductVariation.observed_product_le_of_bound
    (exteriorLaw rows repeats p slots) _ _ (ExtraCutCall.splitRecord rows repeats p slots)
    (OriginalPrefixContinuation.assembledLaw_variation
      (OriginalCutCalls.count rows repeats n (m + 1) + 1)
      rows repeats (cutSlots p slots) ν q hbranch)

theorem observed_totalVariation_le {D Γ : Type*} [Fintype D] [Fintype Γ]
    (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (directions : FiniteDistribution D) (observe : D × Record rows repeats p slots → Γ) :
    ((directions.product (actualLaw rows repeats p slots ν q hbranch)).pushforward observe).totalVariation
        ((directions.product (referenceLaw rows repeats p slots)).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 :=
  CommonProductVariation.observed_product_le_of_bound directions _ _ observe
    (totalVariation_le rows repeats p slots ν q hbranch)

end
end PerfectCompleteness.OriginalExtraCutComparison

end

end OAI
