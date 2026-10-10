import OAI.Computability.PerfectCompleteness.Foundations.ProjectedFiberSquare

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberUpperSeed

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open ProjectedLowerFiber ProjectedFiberSquare

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Direction (rows := rows) upper level d) (arrays : Arrays projected rows)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper (lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

theorem seed_mean_ignore_right (f : UpperTable (rows := rows) slots upper level r → ℝ) :
    (seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).expectation
        (fun seed => f seed.1) =
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation f := by
  unfold seedLaw
  rw [FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro table
  unfold FiniteDistribution.expectation
  change (∑ x, (rightLaw projected upper level d A a arrays known repeats cut σ threshold).weight x *
    f table) = f table
  rw [← Finset.sum_mul,
    (rightLaw projected upper level d A a arrays known repeats cut σ threshold).normalized,
    one_mul]

variable (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (hbranch : ∀ k < n, 0 < branch k)

theorem success_square_le_upperSeed (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d)) :
    success slots projected projection upper level hbranch d A a arrays known
        repeats cut σ useful ρ threshold s ν ^ 2 ≤
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
        (fun table => (ν.product ν).probability
          (restrictedPair slots projected projection upper level hbranch d A a arrays s table)) := by
  have h := success_square_le slots projected projection upper level hbranch d A a arrays known
    repeats cut σ useful ρ threshold s ν
  calc
    _ ≤ _ := h
    _ = _ := seed_mean_ignore_right slots projected upper level d A a arrays known
      repeats cut σ useful ρ threshold (fun table => (ν.product ν).probability
        (restrictedPair slots projected projection upper level hbranch d A a arrays s table))

end
end PerfectCompleteness.ProjectedFiberUpperSeed

end

end OAI
