import OAI.Combinatorics.BalancedRyser.Candidates.CandidateExternalTransport

namespace OAI

open _root_.Balanced _root_.OAI.Balanced CandidateValidityAssembly
open scoped BigOperators

example (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (M : MergedPairs F) (g : Direction F) :
    (externalFailures M g).card ≤ (ExternalAssembly.witnesses g M).card :=
  externalFailures_card_le_witnesses M g

example (F : Type 1) [Field F] [Fintype F] [DecidableEq F]
    (M : MergedPairs F) (g : Direction F) :
    (externalFailures M g).card ≤ (ExternalAssembly.witnesses g M).card :=
  externalFailures_card_le_witnesses M g

example (F : Type 1) [Field F] [Fintype F] [DecidableEq F]
    (g : Direction F) (D : Finset (Direction F)) (a : MergedPairs F) :
    (∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((externalFailures M g).card : ℝ)^0) ≤
    ∑ M : MergedPairs F, (CandidateExposure.exposedLaw D a M).toReal *
      ((ExternalAssembly.witnesses g M).card : ℝ)^0 :=
  externalFailures_moment_le_witnesses g D a 0

example (F : Type) [Field F] [Fintype F] [DecidableEq F] (t : ℝ) :
    offsetEventProbability {M : MergedPairs F | ∃ g,
      t ≤ ((externalFailures M g).card : ℝ)} ≤
    offsetEventProbability {M : MergedPairs F | ∃ g,
      t ≤ ((ExternalAssembly.witnesses g M).card : ℝ)} :=
  externalFailures_some_tail_le t

end OAI
