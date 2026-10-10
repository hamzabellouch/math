import OAI.Computability.PerfectCompleteness.Construction.BucketQuotientAgreement
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalFrozenTablesLemmas
import OAI.Computability.PerfectCompleteness.Sampling.DensityVariation

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAgreementMean

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem probability_product {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A × B → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun a => ν.probability (fun b => event (a, b))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

abbrev Background := HierarchicalMatrixTable.Background (rows := rows) slots upper
abbrev Matrix := HierarchicalMatrixTable.Matrix (rows := rows) slots upper

local instance backgroundFintype : Fintype (Background (rows := rows) slots upper) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype :
    Fintype (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

abbrev PairRecord :=
  Background (rows := rows) slots upper ×
    (Matrix (rows := rows) slots upper × Matrix (rows := rows) slots upper)

abbrev BucketSample :=
  BucketSampler.Direction (rows (Nodes.height upper)) ×
    (BucketSampler.Tape (rows (Nodes.height upper)) (NodeEmbedding.RowSpace slots upper) ×
      NodeEmbedding.RowSpace slots upper)

def bucketLaw (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (BucketSample (rows := rows) slots upper) := by
  letI : Nonempty (BucketSampler.Direction (rows (Nodes.height upper))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact (FiniteDistribution.uniform (BucketSampler.Direction (rows (Nodes.height upper)))).product
    ((BucketSampler.tapeLaw (rows (Nodes.height upper))
      (FiniteDistribution.uniform (NodeEmbedding.RowSpace slots upper))).product
        (FiniteDistribution.uniform (NodeEmbedding.RowSpace slots upper)))

def pairRecord
    (sample : Background (rows := rows) slots upper × BucketSample (rows := rows) slots upper) :
    PairRecord (rows := rows) slots upper :=
  (sample.1,
    (BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots upper)
      (rows (Nodes.height upper)) sample.2.2.1,
    BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots upper)
      (rows (Nodes.height upper)) (Function.update sample.2.2.1 sample.2.1 sample.2.2.2)))

def referenceLaw
    (backgroundLaw : FiniteDistribution (Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (PairRecord (rows := rows) slots upper) :=
  (backgroundLaw.product (bucketLaw slots upper hrows)).pushforward (pairRecord slots upper)

variable (lowerLevel : Nat) {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def collision (record : PairRecord (rows := rows) slots upper) : Bool :=
  TwoResponseCollision.collision
    (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ record.1)
    (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel record.1) record.2.1,
      MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel record.1) record.2.2)

theorem reference_collision_eq_mean
    (backgroundLaw : FiniteDistribution (Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (referenceLaw slots upper backgroundLaw hrows).probability
        (collision slots upper lowerLevel original arrays lower κ σ) =
      backgroundLaw.expectation (fun background => PartialTableInverse.nonzeroAgreement
        (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ background)) := by
  let : Nonempty (BucketSampler.Direction (rows (Nodes.height upper))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  rw [referenceLaw, FiniteDistribution.probability_pushforward, probability_product]
  apply FiniteDistribution.expectation_congr
  intro background
  exact BucketQuotientAgreement.uniform_bucket_collision_probability
    (NodeEmbedding.RowSpace slots upper) (rows (Nodes.height upper))
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ background)

theorem mean_nonzeroAgreement_ge_of_collision
    (backgroundLaw : FiniteDistribution (Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper))
    (sourceLaw : FiniteDistribution (PairRecord (rows := rows) slots upper))
    (b δ : ℝ)
    (hcollision : b ≤ sourceLaw.probability
      (collision slots upper lowerLevel original arrays lower κ σ))
    (hvariation : sourceLaw.totalVariation (referenceLaw slots upper backgroundLaw hrows) ≤ δ) :
    b - δ ≤ backgroundLaw.expectation (fun background => PartialTableInverse.nonzeroAgreement
      (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ background)) := by
  have h := FiniteDistribution.probability_le_add_totalVariation sourceLaw
    (referenceLaw slots upper backgroundLaw hrows)
    (collision slots upper lowerLevel original arrays lower κ σ)
  rw [reference_collision_eq_mean] at h
  linarith

theorem mean_nonzeroAgreement_ge_sixteenth
    (backgroundLaw : FiniteDistribution (Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper))
    (sourceLaw : FiniteDistribution (PairRecord (rows := rows) slots upper)) (c : ℝ)
    (hcollision : c ^ 2 / 8 ≤ sourceLaw.probability
      (collision slots upper lowerLevel original arrays lower κ σ))
    (hvariation : sourceLaw.totalVariation (referenceLaw slots upper backgroundLaw hrows) ≤ c ^ 2 / 16) :
    2 * (c ^ 2 / 32) ≤
      backgroundLaw.expectation (fun background => PartialTableInverse.nonzeroAgreement
        (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ background)) := by
  have h := mean_nonzeroAgreement_ge_of_collision slots upper lowerLevel
    original arrays lower κ σ backgroundLaw hrows sourceLaw (c ^ 2 / 8) (c ^ 2 / 16)
    hcollision hvariation
  linarith

end
end PerfectCompleteness.HierarchicalAgreementMean

end

end OAI
