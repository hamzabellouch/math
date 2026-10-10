import OAI.Computability.PerfectCompleteness.Decoding.BucketUsefulCollision
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalAgreementMean
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness

namespace OAI

section

namespace PerfectCompleteness.HierarchicalUsefulCollision

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

private theorem probability_product_first {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A → Bool) :
    (μ.product ν).probability (fun x => event x.1) = μ.probability event := by
  unfold FiniteDistribution.probability
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  cases he : event a <;>
    simp [FiniteDistribution.product, he, ← Finset.mul_sum, ν.normalized]

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

abbrev Background := HierarchicalAgreementMean.Background (rows := rows) slots upper
abbrev Matrix := HierarchicalAgreementMean.Matrix (rows := rows) slots upper
abbrev Direction := BucketSampler.Direction (rows (Nodes.height upper))
abbrev Tape := BucketSampler.Tape (rows (Nodes.height upper)) (NodeEmbedding.RowSpace slots upper)

local instance backgroundFintype : Fintype (Background (rows := rows) slots upper) :=
  Fintype.ofFinite _

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance valueFintype :
    Fintype (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _

def directionLaw (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (Direction (rows := rows) upper) := by
  letI : Nonempty (Direction (rows := rows) upper) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  exact FiniteDistribution.uniform _

def bucketLaw (ν : FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (HierarchicalAgreementMean.BucketSample (rows := rows) slots upper) :=
  (directionLaw upper hrows).product
    ((BucketSampler.tapeLaw (rows (Nodes.height upper)) ν).product ν)

variable {P : Type*} [Fintype P]

abbrev Sample := (_ : P) × HierarchicalAgreementMean.BucketSample (rows := rows) slots upper

def law (externalLaw : FiniteDistribution P)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (Sample (P := P) (rows := rows) slots upper) :=
  CompletionSoundness.sigmaLaw externalLaw (fun p => bucketLaw slots upper (scalarLaw p) hrows)

def pairRecord (background : P → Background (rows := rows) slots upper)
    (sample : Sample (P := P) (rows := rows) slots upper) :
    HierarchicalAgreementMean.PairRecord (rows := rows) slots upper :=
  HierarchicalAgreementMean.pairRecord slots upper (background sample.1, sample.2)

def pairLaw (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    FiniteDistribution (HierarchicalAgreementMean.PairRecord (rows := rows) slots upper) :=
  (law slots upper externalLaw scalarLaw hrows).pushforward (pairRecord slots upper background)

variable (lowerLevel : Nat) {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

def usefulAccepted (background : Background (rows := rows) slots upper)
    (a : Direction (rows := rows) upper) (tape : Tape (rows := rows) slots upper) : Bool :=
  decide (CanonicalMatrixTable.Accepts (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
    σ a.val (BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots upper)
      (rows (Nodes.height upper)) tape)) &&
    (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ background
      (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots upper)
          (rows (Nodes.height upper)) tape))).isSome

def usefulEvent (background : P → Background (rows := rows) slots upper)
    (sample : Sample (P := P) (rows := rows) slots upper) : Bool :=
  usefulAccepted slots upper lowerLevel original arrays lower κ σ
    (background sample.1) sample.2.1 sample.2.2.1

theorem direction_collision_lower_bound
    (background : Background (rows := rows) slots upper)
    (ν : FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (a : Direction (rows := rows) upper) :
    (BucketSampler.tapeLaw (rows (Nodes.height upper)) ν).probability
        (usefulAccepted slots upper lowerLevel original arrays lower κ σ background a) ^ 2 / 2 ≤
      ((BucketSampler.tapeLaw (rows (Nodes.height upper)) ν).product ν).probability
        (fun z => HierarchicalAgreementMean.collision slots upper lowerLevel
          original arrays lower κ σ
          (HierarchicalAgreementMean.pairRecord slots upper (background, (a, z)))) := by
  exact BucketUsefulCollision.collision_probability_lower_bound
    (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper background) σ
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background)
    (HierarchicalFrozenTables.determined slots upper lowerLevel background) ν
    (fun X => HierarchicalUsefulness.mark slots upper lowerLevel original arrays lower κ
      ⟨background, X⟩ = true) a

theorem useful_probability_eq
    (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (law slots upper externalLaw scalarLaw hrows).probability
        (usefulEvent slots upper lowerLevel original arrays lower κ σ background) =
      externalLaw.expectation (fun p => (directionLaw upper hrows).expectation (fun a =>
        (BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)).probability
          (usefulAccepted slots upper lowerLevel original arrays lower κ σ (background p) a))) := by
  rw [law, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro p
  rw [bucketLaw, probability_product]
  apply FiniteDistribution.expectation_congr
  intro a
  exact probability_product_first
    (BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)) (scalarLaw p)
    (usefulAccepted slots upper lowerLevel original arrays lower κ σ (background p) a)

theorem collision_probability_eq
    (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (pairLaw slots upper externalLaw background scalarLaw hrows).probability
        (HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ) =
      externalLaw.expectation (fun p => (directionLaw upper hrows).expectation (fun a =>
        ((BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)).product
          (scalarLaw p)).probability (fun z =>
            HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ
              (HierarchicalAgreementMean.pairRecord slots upper (background p, (a, z)))))) := by
  rw [pairLaw, FiniteDistribution.probability_pushforward, law,
    CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro p
  exact probability_product (directionLaw upper hrows)
    ((BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)).product (scalarLaw p))
    (fun z => HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ
      (HierarchicalAgreementMean.pairRecord slots upper (background p, z)))

theorem collision_probability_lower_bound
    (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (law slots upper externalLaw scalarLaw hrows).probability
        (usefulEvent slots upper lowerLevel original arrays lower κ σ background) ^ 2 / 2 ≤
      (pairLaw slots upper externalLaw background scalarLaw hrows).probability
        (HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ) := by
  rw [useful_probability_eq, collision_probability_eq]
  apply CollisionAveraging.average_square_bound
  intro p
  apply CollisionAveraging.average_square_bound
  intro a
  exact direction_collision_lower_bound slots upper lowerLevel original arrays lower κ σ
    (background p) (scalarLaw p) a

theorem collision_probability_ge_eighth
    (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ (law slots upper externalLaw scalarLaw hrows).probability
      (usefulEvent slots upper lowerLevel original arrays lower κ σ background)) :
    c ^ 2 / 8 ≤
      (pairLaw slots upper externalLaw background scalarLaw hrows).probability
        (HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ) := by
  have h := collision_probability_lower_bound slots upper lowerLevel original arrays lower κ σ
    externalLaw background scalarLaw hrows
  have hprod : 0 ≤
      ((law slots upper externalLaw scalarLaw hrows).probability
        (usefulEvent slots upper lowerLevel original arrays lower κ σ background) - c / 2) *
      ((law slots upper externalLaw scalarLaw hrows).probability
        (usefulEvent slots upper lowerLevel original arrays lower κ σ background) + c / 2) :=
    mul_nonneg (sub_nonneg.mpr hmass) (by linarith)
  nlinarith

end
end PerfectCompleteness.HierarchicalUsefulCollision

end

end OAI
