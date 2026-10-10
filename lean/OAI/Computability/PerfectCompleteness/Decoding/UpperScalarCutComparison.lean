import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutLaw
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedPrefixComparison

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

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

variable {branch : Nat → Nat} {n j i k t : Nat} {K : Type*} [Fintype K]

abbrev Observation (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  OriginalWholeCutBridge.NumberedRecord rows repeats (p.append r) slots × H (cutSlots p slots)

def originalLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch i k) (hbranch : 0 < branch i) :
    FiniteDistribution (Observation rows repeats p r slots) :=
  ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (OriginalPrefixContinuation.assembledLaw
      (UpperScalarCutCalls.count rows repeats n j (i + 1)) rows repeats
      (cutSlots (p.append r) slots) ν q hbranch)).pushforward
        (numberedObserve rows repeats p r slots)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem originalLaw_eq_mixture (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch i k) (hbranch : 0 < branch i) :
    originalLaw rows repeats p r slots ν q hbranch =
      (OriginalPrefixContinuation.tagLaw ν hbranch).mixture (fun tag =>
        ((OriginalWholeCutLaw.recordLaw rows repeats (p.append r) tag.1 (q tag.2) slots).pushforward
          (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots)).product
            (RecursiveSampler.law F2 repeats (r.append (.step tag.1 (q tag.2)))
              (LeafDomain (cutSlots p slots)))) := by
  unfold originalLaw
  rw [OriginalPrefixContinuation.assembledLaw_eq_mixture, product_mixture_pushforward]
  apply congrArg ((OriginalPrefixContinuation.tagLaw ν hbranch).mixture)
  funext tag
  exact UpperScalarCutLaw.numberedObserve_law rows repeats p r tag.1 (q tag.2) slots

def uniformLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (Observation rows repeats p r slots) :=
  ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (FiniteDistribution.uniform (CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n j (i + 1)))
      (cutSlots (p.append r) slots) rows))).pushforward
        (numberedObserve rows repeats p r slots)

theorem original_uniform_variation (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch i k) (hbranch : 0 < branch i) :
    (originalLaw rows repeats p r slots ν q hbranch).totalVariation
      (uniformLaw rows repeats p r slots) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n j (i + 1)) rows : ℝ) ^ 2 / branch i) / 2 :=
  CommonProductVariation.observed_product_le_of_bound
    (UpperScalarCutLaw.exteriorLaw rows repeats p r slots) _ _
    (numberedObserve rows repeats p r slots)
    (OriginalPrefixContinuation.assembledLaw_variation
      (UpperScalarCutCalls.count rows repeats n j (i + 1)) rows repeats
      (cutSlots (p.append r) slots) ν q hbranch)

variable {Z : Fin (branch i) → Type*} [∀ c, Fintype (Z c)]

def modifiedLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (c : Fin (branch i)) → Z c → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ c z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append r) slots) c s a) (projected c z s a))
    (choiceLaw : (c : Fin (branch i)) → FiniteDistribution (Z c))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    FiniteDistribution (Observation rows repeats p r slots) :=
  ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (ProjectedPrefixComparison.assembledLaw
      (UpperScalarCutCalls.count rows repeats n j (i + 1)) rows
      (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ')).pushforward
        (numberedObserve rows repeats p r slots)

theorem modified_original_variation (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (c : Fin (branch i)) → Z c → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ c z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append r) slots) c s a) (projected c z s a))
    (choiceLaw : (c : Fin (branch i)) → FiniteDistribution (Z c))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : FiniteDistribution K) (q : K → Path branch i k) (hbranch : 0 < branch i) :
    (modifiedLaw rows repeats p r slots projected projection choiceLaw β hβ hβ').totalVariation
      (originalLaw rows repeats p r slots ν q hbranch) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n j (i + 1)) rows : ℝ) - 1)) ^ branch i - 1) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch i t
        (UpperScalarCutCalls.count rows repeats n j (i + 1)) rows : ℝ) ^ 2 / branch i) / 2 :=
  ProjectedPrefixComparison.observed_original_variation
    (UpperScalarCutCalls.count rows repeats n j (i + 1)) rows repeats
    (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ' ν q hbranch
    (UpperScalarCutLaw.exteriorLaw rows repeats p r slots) (numberedObserve rows repeats p r slots)

end
end PerfectCompleteness.UpperScalarCutComparison

end

end OAI
