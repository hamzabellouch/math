import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalUsefulCollision
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Sampling.HierarchicalBackgroundVariation

namespace OAI

section

namespace PerfectCompleteness.HierarchicalUsefulBackground

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

local instance backgroundFintype :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots upper) := Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) := Fintype.ofFinite _

variable {P : Type*} [Fintype P]
  (externalLaw : FiniteDistribution P)
  (background : P → HierarchicalAgreementMean.Background (rows := rows) slots upper)
  (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
  (hrows : 0 < rows (Nodes.height upper))

theorem pairLaw_background :
    (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows).pushforward
        Prod.fst = externalLaw.pushforward background := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, HierarchicalUsefulCollision.pairLaw,
    FiniteDistribution.probability_pushforward, FiniteDistribution.probability_pushforward]
  change (CompletionSoundness.sigmaLaw externalLaw
      (fun p => HierarchicalUsefulCollision.bucketLaw slots upper (scalarLaw p) hrows)).probability
        (fun sample => event (background sample.1)) =
      externalLaw.probability (fun p => event (background p))
  exact CompletionSoundness.sigmaLaw_probability_first externalLaw
    (fun p => HierarchicalUsefulCollision.bucketLaw slots upper (scalarLaw p) hrows)
    (fun p => event (background p))

theorem original_background_variation
    (referenceBackground : FiniteDistribution
      (HierarchicalAgreementMean.Background (rows := rows) slots upper)) :
    (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows).totalVariation
        (HierarchicalAgreementMean.referenceLaw slots upper
          (externalLaw.pushforward background) hrows) ≤
      2 * (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows).totalVariation
        (HierarchicalAgreementMean.referenceLaw slots upper referenceBackground hrows) := by
  have h := HierarchicalBackgroundVariation.original_background_variation slots upper
    (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows)
    referenceBackground hrows
  rw [pairLaw_background] at h
  exact h

theorem original_background_le_of_bound
    (referenceBackground : FiniteDistribution
      (HierarchicalAgreementMean.Background (rows := rows) slots upper)) {error : ℝ}
    (herror : (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows).totalVariation
      (HierarchicalAgreementMean.referenceLaw slots upper referenceBackground hrows) ≤ error) :
    (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows).totalVariation
      (HierarchicalAgreementMean.referenceLaw slots upper
        (externalLaw.pushforward background) hrows) ≤ 2 * error := by
  have h := HierarchicalBackgroundVariation.original_background_le_of_bound slots upper
    (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows)
    referenceBackground hrows herror
  rw [pairLaw_background] at h
  exact h

end
end PerfectCompleteness.HierarchicalUsefulBackground

end

end OAI
