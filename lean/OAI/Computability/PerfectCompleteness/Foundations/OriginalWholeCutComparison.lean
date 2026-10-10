import OAI.Computability.PerfectCompleteness.Foundations.CutContinuationAveraging
import OAI.Computability.PerfectCompleteness.Foundations.OriginalHiddenConditional
import OAI.Computability.PerfectCompleteness.Sampling.NumberedUniformCut

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem totalVariation_le (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < m + 1, 0 < branch k) :
    (CutContinuationAveraging.originalArrayLaw rows repeats p slots hbranch).totalVariation
      (WholeArraySampler.law rows repeats p slots) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1)) rows : ℝ) ^ 2 / branch m) / 2 := by
  rw [CutContinuationAveraging.originalArrayLaw_eq_sigma,
    ← NumberedUniformCut.reconstruct_sigma_uniform rows repeats p slots]
  exact OriginalHiddenConditional.observed_variation
    (OriginalCutCalls.count rows repeats n (m + 1)) rows repeats
    (fun _ : Exterior rows repeats p slots => cutSlots p slots)
    (exteriorLaw rows repeats p slots) hbranch
    (fun z => OriginalWholeCutBridge.reconstruct rows repeats p slots (z.1, z.2))

theorem observed_totalVariation_le {Γ : Type*} [Fintype Γ]
    (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < m + 1, 0 < branch k) (observe : Arrays slots rows → Γ) :
    ((CutContinuationAveraging.originalArrayLaw rows repeats p slots hbranch).pushforward observe).totalVariation ((WholeArraySampler.law rows repeats p slots).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1)) rows : ℝ) ^ 2 / branch m) / 2 :=
  (DensityVariation.variation_pushforward_le _ _ observe).trans
    (totalVariation_le rows repeats p slots hbranch)

theorem conditional_observed_totalVariation_le
    {S Γ : Type*} [Fintype S] [Fintype Γ]
    (rows repeats : Nat → Nat) (p : S → Path branch n (m + 1))
    (slots : S → Slots branch n → Fin t → MixedSupport.Slot)
    (μ : FiniteDistribution S) (hbranch : ∀ k < m + 1, 0 < branch k)
    (observe : (Σ s : S, Arrays (slots s) rows) → Γ) :
    ((CompletionSoundness.sigmaLaw μ (fun s =>
        CutContinuationAveraging.originalArrayLaw rows repeats (p s) (slots s) hbranch)).pushforward observe).totalVariation
      ((CompletionSoundness.sigmaLaw μ (fun s =>
        WholeArraySampler.law rows repeats (p s) (slots s))).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1)) rows : ℝ) ^ 2 / branch m) / 2 := by
  exact ConditionalVariation.observed_sigma_le_const μ
    (fun s => CutContinuationAveraging.originalArrayLaw rows repeats (p s) (slots s) hbranch)
    (fun s => WholeArraySampler.law rows repeats (p s) (slots s))
    _ (fun s => totalVariation_le rows repeats (p s) (slots s) hbranch) observe

end
end PerfectCompleteness.OriginalWholeCutComparison

end

end OAI
