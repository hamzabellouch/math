import OAI.Computability.PerfectCompleteness.Construction.HierarchicalAdviceFromBuckets
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAdviceExperimentLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CandidateCoupling

namespace OAI

section

namespace PerfectCompleteness.HierarchicalBucketFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

local instance backgroundFiberFintype (o : O) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)

local instance rowSpaceFintype (o : O) :
    Fintype (NodeEmbedding.RowSpace (S o).slots (S o).upper) := Fintype.ofFinite _

local instance inputFintype (b : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Input S b) :=
  HierarchicalAdviceFamily.inputFintype S b

local instance inputFiniteDimensional (b : HierarchicalAdviceFamily.Background S) :
    FiniteDimensional F2 (HierarchicalAdviceFamily.Input S b) :=
  HierarchicalAdviceFamily.inputFiniteDimensional S b

local instance valueFintype (b : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S b) :=
  HierarchicalAdviceFamily.valueFintype S b

abbrev PairRecord :=
  (o : O) × HierarchicalAgreementMean.PairRecord (rows := rows) (S o).slots (S o).upper

def collision (κ : ℝ) (z : PairRecord S) : Bool :=
  HierarchicalAgreementMean.collision (S z.1).slots (S z.1).upper (S z.1).lowerLevel
    (S z.1).original (S z.1).arrays (HierarchicalAdviceExperiment.lowerEvent (S z.1))
    κ (S z.1).strategy z.2

def referencePairLaw (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    FiniteDistribution (PairRecord S) :=
  CompletionSoundness.sigmaLaw outer (fun o =>
    HierarchicalAgreementMean.referenceLaw (S o).slots (S o).upper (backgrounds o) (hrows o))

theorem reference_collision_eq_mean (κ : ℝ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    (referencePairLaw S outer backgrounds hrows).probability (collision S κ) =
      (HierarchicalAdviceFamily.backgroundLaw S outer backgrounds).expectation
        (fun b => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceFamily.table S κ b)) := by
  rw [referencePairLaw, CompletionSoundness.sigmaLaw_probability,
    HierarchicalAdviceFamily.backgroundLaw, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro o
  exact HierarchicalAgreementMean.reference_collision_eq_mean
    (S o).slots (S o).upper (S o).lowerLevel (S o).original (S o).arrays
    (HierarchicalAdviceExperiment.lowerEvent (S o)) κ (S o).strategy (backgrounds o) (hrows o)

variable {P : O → Type*} [∀ o, Fintype (P o)]

def actualBackgrounds (externalLaw : (o : O) → FiniteDistribution (P o))
    (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
    (o : O) : FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceFromBuckets.backgroundLaw (S o) (externalLaw o) (background o)

def actualPairLaw (outer : FiniteDistribution O)
    (externalLaw : (o : O) → FiniteDistribution (P o))
    (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
    (scalarLaw : (o : O) → P o →
      FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    FiniteDistribution (PairRecord S) :=
  CompletionSoundness.sigmaLaw outer (fun o =>
    HierarchicalAdviceFromBuckets.pairedLaw (S o) (externalLaw o) (background o) (scalarLaw o) (hrows o))

def usefulMass (κ : ℝ) (outer : FiniteDistribution O)
    (externalLaw : (o : O) → FiniteDistribution (P o))
    (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
    (scalarLaw : (o : O) → P o →
      FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) : ℝ :=
  outer.expectation (fun o => HierarchicalAdviceFromBuckets.usefulProbability (S o) κ
    (externalLaw o) (background o) (scalarLaw o) (hrows o))

variable (κ : ℝ) (outer : FiniteDistribution O)
  (externalLaw : (o : O) → FiniteDistribution (P o))
  (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
  (scalarLaw : (o : O) → P o →
    FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
  (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))

theorem collision_probability_lower_bound :
    usefulMass S κ outer externalLaw background scalarLaw hrows ^ 2 / 2 ≤
      (actualPairLaw S outer externalLaw background scalarLaw hrows).probability (collision S κ) := by
  rw [usefulMass, actualPairLaw, CompletionSoundness.sigmaLaw_probability]
  apply CollisionAveraging.average_square_bound outer
  intro o
  exact HierarchicalUsefulCollision.collision_probability_lower_bound
    (S o).slots (S o).upper (S o).lowerLevel (S o).original (S o).arrays
    (HierarchicalAdviceExperiment.lowerEvent (S o)) κ (S o).strategy
    (externalLaw o) (background o) (scalarLaw o) (hrows o)

theorem collision_probability_ge_eighth (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulMass S κ outer externalLaw background scalarLaw hrows) :
    c ^ 2 / 8 ≤
      (actualPairLaw S outer externalLaw background scalarLaw hrows).probability (collision S κ) := by
  rw [actualPairLaw, CompletionSoundness.sigmaLaw_probability]
  refine CollisionAveraging.eighth_square_bound outer
    (fun o => HierarchicalAdviceFromBuckets.usefulProbability (S o) κ
      (externalLaw o) (background o) (scalarLaw o) (hrows o)) _ ?_ c hc hmass
  intro o
  exact HierarchicalUsefulCollision.collision_probability_lower_bound
    (S o).slots (S o).upper (S o).lowerLevel (S o).original (S o).arrays
    (HierarchicalAdviceExperiment.lowerEvent (S o)) κ (S o).strategy
    (externalLaw o) (background o) (scalarLaw o) (hrows o)

theorem mean_agreement_ge
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulMass S κ outer externalLaw background scalarLaw hrows)
    (hpaired : (actualPairLaw S outer externalLaw background scalarLaw hrows).totalVariation
      (referencePairLaw S outer backgrounds hrows) ≤ c ^ 2 / 16) :
    c ^ 2 / 16 ≤ (HierarchicalAdviceFamily.backgroundLaw S outer backgrounds).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceFamily.table S κ b)) := by
  have hcollision := collision_probability_ge_eighth S κ outer externalLaw background scalarLaw
    hrows c hc hmass
  have htransfer := FiniteDistribution.probability_le_add_totalVariation
    (actualPairLaw S outer externalLaw background scalarLaw hrows)
    (referencePairLaw S outer backgrounds hrows) (collision S κ)
  rw [reference_collision_eq_mean] at htransfer
  linarith

theorem mean_agreement_ge_actual_background (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulMass S κ outer externalLaw background scalarLaw hrows)
    (hpaired : (actualPairLaw S outer externalLaw background scalarLaw hrows).totalVariation
      (referencePairLaw S outer (actualBackgrounds S externalLaw background) hrows) ≤ c ^ 2 / 16) :
    c ^ 2 / 16 ≤
      (HierarchicalAdviceFamily.backgroundLaw S outer (actualBackgrounds S externalLaw background)).expectation
        (fun b => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceFamily.table S κ b)) :=
  mean_agreement_ge S κ outer externalLaw background scalarLaw hrows
    (actualBackgrounds S externalLaw background) c hc hmass hpaired

end
end PerfectCompleteness.HierarchicalBucketFamily

end

end OAI
