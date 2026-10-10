import OAI.Computability.PerfectCompleteness.Construction.OriginalHiddenChild
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas

namespace OAI

section

namespace PerfectCompleteness.OriginalHiddenConditional

open RecursiveSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games CompletionSoundness

noncomputable section

variable {S : Type*} [Fintype S] {branch : Nat → Nat} {n t : Nat}

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : S → Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (μ : FiniteDistribution S) (hbranch : ∀ k < n + 1, 0 < branch k)
    (observe : (Σ s : S, CutChildGrouping.Assembled (C := Fin calls) (slots s) rows) → Γ) :
    ((sigmaLaw μ (fun s => OriginalHiddenChild.sourceLaw calls rows repeats (slots s) hbranch)).pushforward (fun z => observe ⟨z.1,
        OriginalHiddenChild.observed calls rows repeats (slots z.1) z.2⟩)).totalVariation
      ((sigmaLaw μ (fun s => FiniteDistribution.uniform
        (CutChildGrouping.Assembled (C := Fin calls) (slots s) rows))).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        branch n) / 2 := by
  have hleft :
      (sigmaLaw μ (fun s => OriginalHiddenChild.sourceLaw calls rows repeats (slots s) hbranch)).pushforward (fun z => observe ⟨z.1,
          OriginalHiddenChild.observed calls rows repeats (slots z.1) z.2⟩) =
      (sigmaLaw μ (fun s =>
        (OriginalHiddenChild.sourceLaw calls rows repeats (slots s) hbranch).pushforward
          (OriginalHiddenChild.observed calls rows repeats (slots s)))).pushforward observe := by
    calc
      _ = ((sigmaLaw μ (fun s =>
          OriginalHiddenChild.sourceLaw calls rows repeats (slots s) hbranch)).pushforward
          (fun z => (⟨z.1, OriginalHiddenChild.observed calls rows repeats (slots z.1) z.2⟩ :
            Σ s : S, CutChildGrouping.Assembled (C := Fin calls) (slots s) rows))).pushforward observe := (FiniteDistribution.pushforward_comp _ _ _).symm
      _ = _ := congrArg
        (fun law : FiniteDistribution
          (Σ s : S, CutChildGrouping.Assembled (C := Fin calls) (slots s) rows) =>
            law.pushforward observe)
        (SigmaObservation.pushforward_fiber
          (X := fun s => OriginalHiddenChild.Tape calls rows repeats (slots s))
          (Y := fun s => CutChildGrouping.Assembled (C := Fin calls) (slots s) rows)
          μ (fun s => OriginalHiddenChild.sourceLaw calls rows repeats (slots s) hbranch)
          (fun s => OriginalHiddenChild.observed calls rows repeats (slots s)))
  rw [hleft]
  apply ConditionalVariation.observed_sigma_le_const
  intro s
  simpa only [id_eq, FiniteDistribution.pushforward_id] using
    OriginalHiddenChild.observed_variation calls rows repeats (slots s) hbranch id

end
end PerfectCompleteness.OriginalHiddenConditional

end

end OAI
