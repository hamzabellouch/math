import OAI.Computability.PerfectCompleteness.Foundations.ProjectedPrefixComparison
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas

namespace OAI

section

namespace PerfectCompleteness.ProjectedPrefixConditional

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n k t : Nat}
  {S Γ : Type*} [Fintype S] [Fintype Γ]
  {K E : S → Type*} [∀ s, Fintype (K s)] [∀ s, Fintype (E s)]
  {Z : S → Fin (branch n) → Type*} [∀ s i, Fintype (Z s i)]

theorem observed_original_variation (calls : Nat) (rows repeats : Nat → Nat)
    (slots : S → Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (s : S) → (i : Fin (branch n)) → Z s i →
      Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ s i z x j,
      MixedSupport.Projection (childSlots (slots s) i x j) (projected s i z x j))
    (choiceLaw : (s : S) → (i : Fin (branch n)) → FiniteDistribution (Z s i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (ν : (s : S) → FiniteDistribution (K s))
    (q : (s : S) → K s → Path branch n k) (hbranch : 0 < branch n)
    (source : FiniteDistribution S) (exterior : (s : S) → FiniteDistribution (E s))
    (observe : (Σ s : S, E s × CutChildGrouping.Assembled (C := Fin calls) (slots s) rows) → Γ) :
    ((CompletionSoundness.sigmaLaw source (fun s =>
      (exterior s).product (ProjectedPrefixComparison.assembledLaw calls rows (slots s)
        (projected s) (p s) (choiceLaw s) β hβ hβ'))).pushforward observe).totalVariation
      ((CompletionSoundness.sigmaLaw source (fun s =>
        (exterior s).product (OriginalPrefixContinuation.assembledLaw calls rows repeats
          (slots s) (ν s) (q s) hbranch))).pushforward observe) ≤
      Real.sqrt ((1 + β ^ 2 * ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^
        branch n - 1) / 2 +
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 / branch n) / 2 := by
  refine ConditionalVariation.observed_sigma_le_const source _ _ _ ?_ observe
  intro s
  rw [CommonProductVariation.product_totalVariation]
  exact ProjectedPrefixComparison.original_variation calls rows repeats (slots s)
    (projected s) (p s) (choiceLaw s) β hβ hβ' (ν s) (q s) hbranch

end
end PerfectCompleteness.ProjectedPrefixConditional

end

end OAI
