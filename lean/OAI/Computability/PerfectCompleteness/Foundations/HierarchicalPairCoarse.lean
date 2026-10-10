import OAI.Computability.PerfectCompleteness.Algebra.MatrixRowQuotientLaw
import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAgreementMean
import OAI.Computability.PerfectCompleteness.Sampling.CommonProductVariationLemmas
import OAI.Computability.PerfectCompleteness.Sampling.RationalFiniteLawLemmas

namespace OAI

section

namespace PerfectCompleteness.HierarchicalPairCoarse

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

private theorem probability_product {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A × B → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun a => ν.probability (fun b => event (a, b))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

private theorem product_swap {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward (Equiv.prodComm A B) = ν.product μ := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  exact mul_comm _ _

private theorem product_fst {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward Prod.fst = μ := by
  calc
    _ = ((μ.product ν).pushforward (Equiv.prodComm A B)).pushforward Prod.snd :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by rw [product_swap, FiniteDistribution.product_pushforward_snd]

private theorem attach_observation {A B C Γ : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype Γ]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (g : B → C) (f : A × C → Γ) :
    (μ.product ν).pushforward (fun z => f (z.1, g z.2)) =
      (μ.product (ν.pushforward g)).pushforward f := by
  have h : (μ.product ν).pushforward (fun z => (z.1, g z.2)) =
      μ.product (ν.pushforward g) := by
    simpa only [id_eq, FiniteDistribution.pushforward_id] using
      FiniteDistribution.product_pushforward μ ν id g
  calc
    _ = ((μ.product ν).pushforward (fun z => (z.1, g z.2))).pushforward f :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := congrArg (fun ρ : FiniteDistribution (A × C) => ρ.pushforward f) h

variable {branch rows : Nat → Nat} {n t : Nat} {Ω : Type*} [Fintype Ω]
  (S : HierarchicalAdviceExperiment.Experiment branch rows n t Ω)

abbrev PairRecord := HierarchicalAgreementMean.PairRecord (rows := rows) S.slots S.upper
abbrev Matrix := HierarchicalMatrixTable.Matrix (rows := rows) S.slots S.upper
abbrev OldRecord := HierarchicalAdviceExperiment.Background S × Matrix S

local instance backgroundFintype : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace S.slots S.upper) :=
  Fintype.ofFinite _

local instance inputFintype :
    (b : HierarchicalAdviceExperiment.Background S) →
      Fintype (HierarchicalAdviceExperiment.Input S b) := fun _ => linearMapFintype

def oldRecord (record : PairRecord S) : OldRecord S := (record.1, record.2.1)

def coarseOld (record : OldRecord S) : HierarchicalAdviceExperiment.Coarse S :=
  ⟨record.1, MatrixRowQuotient.projectMatrix
    (HierarchicalFrozenTables.knownRows S.slots S.upper S.lowerLevel record.1) record.2⟩

def coarse (record : PairRecord S) : HierarchicalAdviceExperiment.Coarse S :=
  coarseOld S (oldRecord S record)

def observeOld (r : Nat)
    (sample : HierarchicalAdviceExperiment.Advice S r × OldRecord S) :
    HierarchicalAdviceExperiment.Coarse S × HierarchicalAdviceExperiment.Advice S r :=
  (coarseOld S sample.2, sample.1)

def observe (r : Nat)
    (sample : HierarchicalAdviceExperiment.Advice S r × PairRecord S) :
    HierarchicalAdviceExperiment.Coarse S × HierarchicalAdviceExperiment.Advice S r :=
  (coarse S sample.2, sample.1)

private theorem bucket_oldMatrix_law (hrows : 0 < rows (Nodes.height S.upper)) :
    (HierarchicalAgreementMean.bucketLaw S.slots S.upper hrows).pushforward
        (fun sample => BucketMatrixResampling.assembledMatrix
          (NodeEmbedding.RowSpace S.slots S.upper) (rows (Nodes.height S.upper)) sample.2.1) =
      FiniteDistribution.uniform (Matrix S) := by
  let : Nonempty (BucketSampler.Direction (rows (Nodes.height S.upper))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  let directions := FiniteDistribution.uniform (BucketSampler.Direction (rows (Nodes.height S.upper)))
  let buckets := BucketSampler.tapeLaw (rows (Nodes.height S.upper))
    (FiniteDistribution.uniform (NodeEmbedding.RowSpace S.slots S.upper))
  let fresh := FiniteDistribution.uniform (NodeEmbedding.RowSpace S.slots S.upper)
  have hdrop : (HierarchicalAgreementMean.bucketLaw S.slots S.upper hrows).pushforward
      (fun sample => sample.2.1) = buckets := by
    calc
      _ = ((directions.product (buckets.product fresh)).pushforward Prod.snd).pushforward
          Prod.fst := (FiniteDistribution.pushforward_comp _ _ _).symm
      _ = _ := by rw [FiniteDistribution.product_pushforward_snd, product_fst]
  calc
    _ = ((HierarchicalAgreementMean.bucketLaw S.slots S.upper hrows).pushforward
        (fun sample => sample.2.1)).pushforward
          (BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace S.slots S.upper)
            (rows (Nodes.height S.upper))) := (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = buckets.pushforward
        (BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace S.slots S.upper)
          (rows (Nodes.height S.upper))) := by rw [hdrop]
    _ = _ := BucketMatrixResampling.uniform_assembledMatrix_law
      (NodeEmbedding.RowSpace S.slots S.upper) (rows (Nodes.height S.upper))

theorem reference_oldRecord_law
    (backgroundLaw : FiniteDistribution (HierarchicalAdviceExperiment.Background S))
    (hrows : 0 < rows (Nodes.height S.upper)) :
    (HierarchicalAgreementMean.referenceLaw S.slots S.upper backgroundLaw hrows).pushforward
        (oldRecord S) = backgroundLaw.product (FiniteDistribution.uniform (Matrix S)) := by
  unfold HierarchicalAgreementMean.referenceLaw
  rw [FiniteDistribution.pushforward_comp]
  change (backgroundLaw.product (HierarchicalAgreementMean.bucketLaw S.slots S.upper hrows)).pushforward
    (fun sample => (sample.1,
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace S.slots S.upper)
        (rows (Nodes.height S.upper)) sample.2.2.1)) = _
  have h := FiniteDistribution.product_pushforward backgroundLaw
    (HierarchicalAgreementMean.bucketLaw S.slots S.upper hrows) id
    (fun sample => BucketMatrixResampling.assembledMatrix
      (NodeEmbedding.RowSpace S.slots S.upper) (rows (Nodes.height S.upper)) sample.2.1)
  simpa only [id_eq, FiniteDistribution.pushforward_id, bucket_oldMatrix_law] using h

theorem uniform_projectMatrix (background : HierarchicalAdviceExperiment.Background S) :
    (FiniteDistribution.uniform (Matrix S)).pushforward
        (MatrixRowQuotient.projectMatrix
          (HierarchicalFrozenTables.knownRows S.slots S.upper S.lowerLevel background)) =
      FiniteDistribution.uniform
        (HierarchicalAdviceExperiment.Input S background →ₗ[F2] Block rows S.upper) :=
  UniformLinearImage.uniform_pushforward_linearMap
    (MatrixRowQuotientLaw.projectMatrixLinear
      (HierarchicalFrozenTables.knownRows S.slots S.upper S.lowerLevel background))
    (MatrixRowQuotient.projectMatrix_surjective
      (HierarchicalFrozenTables.knownRows S.slots S.upper S.lowerLevel background))

theorem observe_oldRecord_law (μ : FiniteDistribution (PairRecord S)) (r : Nat) :
    ((HierarchicalAdviceExperiment.adviceLaw S r).product μ).pushforward (observe S r) =
      ((HierarchicalAdviceExperiment.adviceLaw S r).product (μ.pushforward (oldRecord S))).pushforward
        (observeOld S r) :=
  attach_observation (HierarchicalAdviceExperiment.adviceLaw S r) μ (oldRecord S) (observeOld S r)

theorem reference_observe_law
    (backgroundLaw : FiniteDistribution (HierarchicalAdviceExperiment.Background S))
    (hrows : 0 < rows (Nodes.height S.upper)) (r : Nat) :
    ((HierarchicalAdviceExperiment.adviceLaw S r).product
      (HierarchicalAgreementMean.referenceLaw S.slots S.upper backgroundLaw hrows)).pushforward
        (observe S r) =
      (HierarchicalAdviceExperiment.referenceLaw S backgroundLaw r).pushforward
        (HierarchicalAdviceExperiment.referenceObserve S r) := by
  rw [observe_oldRecord_law, reference_oldRecord_law]
  apply SigmaObservation.eq_of_probability_eq
  intro event
  calc
    _ = (HierarchicalAdviceExperiment.adviceLaw S r).expectation (fun advice =>
        backgroundLaw.expectation (fun background =>
          (FiniteDistribution.uniform (Matrix S)).probability (fun X =>
            event (⟨background, MatrixRowQuotient.projectMatrix
              (HierarchicalFrozenTables.knownRows S.slots S.upper S.lowerLevel background) X⟩,
              advice)))) := by
      rw [FiniteDistribution.probability_pushforward, probability_product]
      apply FiniteDistribution.expectation_congr
      intro advice
      exact probability_product backgroundLaw (FiniteDistribution.uniform (Matrix S)) _
    _ = backgroundLaw.expectation (fun background =>
        (HierarchicalAdviceExperiment.adviceLaw S r).expectation (fun advice =>
          (FiniteDistribution.uniform (Matrix S)).probability (fun X =>
            event (⟨background, MatrixRowQuotient.projectMatrix
              (HierarchicalFrozenTables.knownRows S.slots S.upper S.lowerLevel background) X⟩,
              advice)))) := FiniteDistribution.expectation_comm _ _ _
    _ = backgroundLaw.expectation (fun background =>
        (HierarchicalAdviceExperiment.adviceLaw S r).expectation (fun advice =>
          (FiniteDistribution.uniform
            (HierarchicalAdviceExperiment.Input S background →ₗ[F2] Block rows S.upper)).probability
              (fun X => event (⟨background, X⟩, advice)))) := by
      apply FiniteDistribution.expectation_congr
      intro background
      apply FiniteDistribution.expectation_congr
      intro advice
      have h := congrArg
        (fun μ : FiniteDistribution
            (HierarchicalAdviceExperiment.Input S background →ₗ[F2] Block rows S.upper) =>
          μ.probability (fun X => event (⟨background, X⟩, advice)))
        (uniform_projectMatrix S background)
      simpa only [FiniteDistribution.probability_pushforward] using h
    _ = _ := by
      symm
      rw [FiniteDistribution.probability_pushforward]
      change (CompletionSoundness.sigmaLaw backgroundLaw
        (fun background => GoodAdviceEvents.law (HierarchicalAdviceExperiment.Input S background)
          (Block rows S.upper) r)).probability
            (fun sample => event (⟨sample.1, sample.2.2⟩, sample.2.1)) = _
      rw [CompletionSoundness.sigmaLaw_probability]
      apply FiniteDistribution.expectation_congr
      intro background
      exact probability_product (HierarchicalAdviceExperiment.adviceLaw S r)
        (FiniteDistribution.uniform
          (HierarchicalAdviceExperiment.Input S background →ₗ[F2] Block rows S.upper)) _

theorem observed_totalVariation_le (μ : FiniteDistribution (PairRecord S))
    (backgroundLaw : FiniteDistribution (HierarchicalAdviceExperiment.Background S))
    (hrows : 0 < rows (Nodes.height S.upper)) (r : Nat) :
    (((HierarchicalAdviceExperiment.adviceLaw S r).product μ).pushforward (observe S r)).totalVariation
        ((HierarchicalAdviceExperiment.referenceLaw S backgroundLaw r).pushforward
          (HierarchicalAdviceExperiment.referenceObserve S r)) ≤
      μ.totalVariation (HierarchicalAgreementMean.referenceLaw S.slots S.upper backgroundLaw hrows) := by
  rw [← reference_observe_law S backgroundLaw hrows r]
  exact CommonProductVariation.observed_product_le (HierarchicalAdviceExperiment.adviceLaw S r)
    μ (HierarchicalAgreementMean.referenceLaw S.slots S.upper backgroundLaw hrows) (observe S r)

theorem original_observe_law_of_oldRecord (μ : FiniteDistribution (PairRecord S)) (r : Nat)
    (hmarginal : μ.pushforward (oldRecord S) = S.original.pushforward
      (fun x => (HierarchicalAdviceExperiment.background S x, HierarchicalAdviceExperiment.matrix S x))) :
    ((HierarchicalAdviceExperiment.adviceLaw S r).product μ).pushforward (observe S r) =
      (HierarchicalAdviceExperiment.originalLaw S r).pushforward
        (HierarchicalAdviceExperiment.observe S r) := by
  rw [observe_oldRecord_law, hmarginal]
  rw [← attach_observation (HierarchicalAdviceExperiment.adviceLaw S r) S.original
    (fun x => (HierarchicalAdviceExperiment.background S x, HierarchicalAdviceExperiment.matrix S x))
    (observeOld S r)]
  calc
    _ = (((HierarchicalAdviceExperiment.adviceLaw S r).product S.original).pushforward
        (Equiv.prodComm (HierarchicalAdviceExperiment.Advice S r) Ω)).pushforward
          (HierarchicalAdviceExperiment.observe S r) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by simp only [product_swap, HierarchicalAdviceExperiment.originalLaw]

theorem original_totalVariation_le_of_oldRecord (μ : FiniteDistribution (PairRecord S))
    (backgroundLaw : FiniteDistribution (HierarchicalAdviceExperiment.Background S))
    (hrows : 0 < rows (Nodes.height S.upper)) (r : Nat)
    (hmarginal : μ.pushforward (oldRecord S) = S.original.pushforward
      (fun x => (HierarchicalAdviceExperiment.background S x, HierarchicalAdviceExperiment.matrix S x))) :
    ((HierarchicalAdviceExperiment.originalLaw S r).pushforward
        (HierarchicalAdviceExperiment.observe S r)).totalVariation
      ((HierarchicalAdviceExperiment.referenceLaw S backgroundLaw r).pushforward
        (HierarchicalAdviceExperiment.referenceObserve S r)) ≤
      μ.totalVariation (HierarchicalAgreementMean.referenceLaw S.slots S.upper backgroundLaw hrows) := by
  rw [← original_observe_law_of_oldRecord S μ r hmarginal]
  exact observed_totalVariation_le S μ backgroundLaw hrows r

end
end PerfectCompleteness.HierarchicalPairCoarse

end

end OAI
