import OAI.Computability.PerfectCompleteness.Construction.BucketFullAgreement
import OAI.Computability.PerfectCompleteness.Decoding.HierarchicalLowerInverseLemmas
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedLowerUniformCollision

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

private theorem expectation_uniform_eq_expect {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    (FiniteDistribution.uniform A).expectation f = 𝔼 x : A, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

section Uniform

variable {Ω Y : Type*} [Fintype Y]
  (V : Submodule F2 (Ω → F2)) [Fintype V] [FiniteDimensional F2 V]
  (ℓ : Nat) [Nonempty (BucketSampler.Direction ℓ)]

def uniformLaw : FiniteDistribution
    (BucketSampler.Direction ℓ × (BucketMatrixResampling.Matrix V ℓ × V)) :=
  (FiniteDistribution.uniform (BucketSampler.Direction ℓ)).product
    ((FiniteDistribution.uniform (BucketMatrixResampling.Matrix V ℓ)).product
      (FiniteDistribution.uniform V))

def uniformCollision (f : BucketMatrixResampling.Matrix V ℓ → Option Y)
    (x : BucketSampler.Direction ℓ × (BucketMatrixResampling.Matrix V ℓ × V)) : Bool :=
  TwoResponseCollision.collision f
    (x.2.1, EvaluationMatrix.shift V x.2.1 x.1.val x.2.2)

theorem uniform_collision_eq (f : BucketMatrixResampling.Matrix V ℓ → Option Y) :
    (uniformLaw V ℓ).probability (uniformCollision V ℓ f) =
      PartialTableInverse.nonzeroAgreement f := by
  unfold uniformLaw uniformCollision
  rw [BucketQuotientAgreement.probability_collision_eq_expectation]
  simp only [FiniteDistribution.expectation_product, expectation_uniform_eq_expect]
  calc
    _ = FiniteRangeInverse.agreement f := by
      unfold FiniteRangeInverse.agreement
      refine Finset.expect_congr (ι := BucketSampler.Direction ℓ) ?_ ?_
      · ext a
        simp only [Finset.mem_univ]
      intro a _
      rfl
    _ = _ := FiniteRangeInverse.agreement_eq_nonzeroAgreement f

end Uniform

variable {δ : ℚ} (plan : FixedRows.Plan δ) (hδ : 0 < δ)
  {branch : Nat → Nat} {t : Nat}
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := FixedRows.rows plan) slots upper)

local instance lowerHFintype (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _

local instance upperDualFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper

variable (hbranch : ∀ k < plan.depth, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (useful : (bg : HierarchicalMatrixTable.Background
      (rows := FixedRows.rows plan) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel bg → Prop)

include hbranch σ useful

local instance directionNonempty (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Nonempty (BucketSampler.Direction
      (FixedRows.rows plan (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))) :=
  ⟨BucketUniform.coordinateDirection ⟨0,
    lt_of_lt_of_le Nat.zero_lt_one
      (plan.rows_pos (plan.depth -
        Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))⟩⟩

theorem supported_collision_lt {adviceRows : Nat}
    (density : ℝ) (hdensity : 0 < density)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := FixedRows.rows plan) slots upper)
    (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input
      (rows := FixedRows.rows plan) slots upper lowerLevel adviceRows →
        HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper lowerLevel σ useful
      adviceRows density).weight table ≠ 0) :
    (uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
      (FixedRows.rows plan (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability
        (uniformCollision _ _
        (HierarchicalLowerInverse.matrixTable slots upper lowerLevel background d upperMatrix A
          (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d
            (FixedRows.cutoff plan hδ) table))) <
      UpperParameterScalars.gamma (InitialParameters.useful δ) plan.density
        (InitialParameters.inverse δ) plan.order
        (FixedRows.rows plan (Nodes.height upper)) ^ 2 / 8 := by
  rw [uniform_collision_eq]
  exact HierarchicalFixedLowerInverse.supported_upper_matrixTable_agreement_lt
    plan hδ slots upper lowerLevel background hbranch σ useful density hdensity
    d upperMatrix A table hsupport

end
end PerfectCompleteness.FixedLowerUniformCollision

end

end OAI
