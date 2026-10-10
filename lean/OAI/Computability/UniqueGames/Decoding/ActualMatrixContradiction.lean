import OAI.Computability.UniqueGames.Decoding.ActualProjectedTransfer
import OAI.Computability.UniqueGames.Decoding.ActualSeedSamplingLemmas
import OAI.Computability.UniqueGames.PCP.SourceIncidence

namespace OAI

section

/-! The contradiction uses the same actual seed and local decoder on both
sides. Its lower bound comes from full-table variation followed by visible
conditioning; its upper bound comes from the exact incidence sampler. -/

namespace UniqueGamesTheorem.Decoder.ActualMatrixContradiction

open Integration.BinaryLinear Reduction ActualSource Foundations.Games
open scoped BigOperators Classical

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] Fintype.ofFinite

variable {k s d r : ℕ}

private theorem univ_fintype_eq {X : Type*} (a b : Fintype X) :
    @Finset.univ X a = @Finset.univ X b :=
  congrArg (fun t : Fintype X => @Finset.univ X t) (Subsingleton.elim a b)

private def expectationOf {X : Type*} {i : Fintype X}
    (μ : @FiniteDistribution X i) (f : X → ℝ) : ℝ :=
  @FiniteDistribution.expectation X i μ f

private theorem card_to_natCard (X : Type*) (i : Fintype X) :
    @Fintype.card X i = Nat.card X :=
  (@Nat.card_eq_fintype_card X i).symm

theorem law_expectation_eq (S : Source) (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (f : ActualSeedEvents.Seed S k s d r → ℝ) :
    expectationOf (ActualSeedEvents.law S k s d r β hβ hβ') f =
      expectationOf (AdviceLaw.fullSeedLaw (V := Alphabet s × Vector d)
        (FiniteDistribution.uniform (Fin k → Fin S.occurrences))
        (FiniteDistribution.uniform (Alphabet s →ₗ[F2] Vector r)) β hβ hβ') f := by
  simp only [expectationOf, FiniteDistribution.expectation, ActualSeedEvents.law,
    AdviceLaw.fullSeedLaw, FiniteDistribution.product, FiniteDistribution.uniform]

theorem contradiction (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2 ^ s))
    (α g₀ β : ℝ) (hα : 0 < α)
    (hsmall : 1 / (2 : ℝ) ^ (s - r) < α / 8)
    (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (hgood : g₀ ≤ ActualGoodRows.adviceMass S k s d r labeling α)
    (hvariation : ActualProjectedTransfer.slopeVariation k s d β ≤
      ConstantSelection.variationBudget α g₀ s r)
    (hrate : (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k <
      ConstantSelection.decodingMass α g₀ s r)
    (hdistinct : S.DistinctNames)
    (hopt : Clean.IncidenceGap.parityValue (ActualAdviceUpper.sourceIncidence S)
      (FiniteDistribution.uniform (Fin S.occurrences)) ≤ (4 : ℝ) / 5) : False := by
  have hlower := ActualProjectedTransfer.actual_success_lower S labeling α g₀ β
    hα hsmall hβ hβ' hgood hvariation
  have hnames : ∀ o i j, (ActualAdviceUpper.sourceIncidence S).name o i =
      (ActualAdviceUpper.sourceIncidence S).name o j → i = j :=
    Outer.SourceIncidence.names_distinct S hdistinct
  have hupper := ActualSeedSampling.fullSeedLaw_upper S labeling
    (SelectedPolicies.goodPredicate S labeling α hα hsmall) β hβ hβ' hnames hopt
  have hbound : ConstantSelection.decodingMass α g₀ s r ≤
      (1 - (β / (2 : ℝ) ^ (d + r)) / 3600) ^ k := by
    apply hlower.trans
    change expectationOf (ActualSeedEvents.law S k s d r β hβ hβ') _ ≤ _
    rw [law_expectation_eq]
    exact hupper
  exact (not_lt_of_ge hbound) hrate

end
end UniqueGamesTheorem.Decoder.ActualMatrixContradiction

end

end OAI
