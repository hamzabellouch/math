import OAI.Computability.PerfectCompleteness.Construction.HiddenBucketBias
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryAveraging
import OAI.Computability.PerfectCompleteness.Sampling.StoppedUsefulPairLaw

namespace OAI

section

namespace PerfectCompleteness.StoppedBucketUsefulProbability

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem probability_product_fst {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A → Bool) :
    (μ.product ν).probability (fun z => event z.1) = μ.probability event := by
  have h := FiniteDistribution.probability_pushforward (μ.product ν) Prod.fst event
  rw [HiddenBucketBias.product_fst] at h
  exact h.symm

variable {branch : Nat → Nat} {N j i t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
  (chosen : Fin (branch j)) (q : Path branch j i)
  (native right : Slots branch N → Fin t → MixedSupport.Slot)
  (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace native (upperNode p)) :=
  Fintype.ofFinite _

local instance backgroundFintype :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) native (upperNode p)) :=
  Fintype.ofFinite _

variable (hrows : 0 < rows (j + 1)) (lowerLevel : Nat) {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays native rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch N t))

theorem usefulEvent_observe
    (sample : StoppedUsefulPairLaw.Sample rows repeats p chosen q right) :
    HierarchicalUsefulCollision.usefulEvent native (upperNode p) lowerLevel
        original arrays lowerEvent κ σ
        (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection)
        (StoppedUsefulPairLaw.observe rows repeats p chosen q native right projection sample) =
      HierarchicalUsefulCollision.usefulAccepted native (upperNode p) lowerLevel
        original arrays lowerEvent κ σ
        (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection
          (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection sample.2.1).1)
        (CutNodeRows.directionEquiv rows p sample.1)
        (CutNodeRows.bucketTapeEquiv rows p native
          (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection sample.2.1).2) :=
  rfl

theorem useful_probability_eq :
    (HierarchicalUsefulCollision.law native (upperNode p)
      (StoppedUsefulPairLaw.externalLaw rows repeats p chosen q right)
      (StoppedUsefulPairLaw.scalarLaw rows repeats p chosen q native right projection)
      (by simpa only [upperNode_height] using hrows)).probability
        (HierarchicalUsefulCollision.usefulEvent native (upperNode p) lowerLevel
          original arrays lowerEvent κ σ
          (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection)) =
      (StoppedUsefulPairLaw.directionLaw rows j hrows).expectation (fun a =>
        (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right).probability
          (fun tape => HierarchicalUsefulCollision.usefulAccepted native (upperNode p) lowerLevel
            original arrays lowerEvent κ σ
            (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection
              (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).1)
            (CutNodeRows.directionEquiv rows p a)
            (CutNodeRows.bucketTapeEquiv rows p native
              (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).2))) := by
  rw [← StoppedUsefulPairLaw.observe_law rows repeats p chosen q native right projection hrows,
    FiniteDistribution.probability_pushforward]
  simp_rw [usefulEvent_observe]
  rw [StoppedUsefulPairLaw.actualLaw, PreliminaryAveraging.probability_product]
  apply FiniteDistribution.expectation_congr
  intro a
  exact probability_product_fst
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right)
    (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right)))
    (fun tape => HierarchicalUsefulCollision.usefulAccepted native (upperNode p) lowerLevel
      original arrays lowerEvent κ σ
      (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection
        (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).1)
      (CutNodeRows.directionEquiv rows p a)
      (CutNodeRows.bucketTapeEquiv rows p native
        (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).2))

end
end PerfectCompleteness.StoppedBucketUsefulProbability

end

end OAI
