import OAI.Computability.PerfectCompleteness.Decoding.ProjectedFiberUpperSeed
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedFiberBackground

namespace OAI

section

namespace PerfectCompleteness.LowerProjectedFiberAverage

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

private theorem probability_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (event : X × Y → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (path : Path branch n (m + 1))
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats path projected)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

abbrev Background := LowerCutFiberDisintegration.Background rows repeats path projected a

def backgroundLaw : FiniteDistribution (Background (repeats := repeats) path projected a) :=
  (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats path projected)).product
    (FiniteDistribution.uniform (LowerCutFiberDisintegration.Quotient rows path projected a))

def baseline (bg : Background (repeats := repeats) path projected a) : Arrays projected rows :=
  LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior bg 0

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)

def readForm (s : Nat) (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r)
    (arrays : Arrays projected rows) :=
  (LowerCutDecoderForm.answer slots upper level d hbranch A table s
    (ChildBlockProjection.arraysPullback rows projection arrays)).map
    (OddListExtraction.multiplicationForm
      (HierarchicalDecoderTables.LowerH slots upper level d))

def collision (s : Nat) (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r)
    (pair : Arrays projected rows × Arrays projected rows) : Bool :=
  BilinearCollisionTransfer.restrictedCollision
    (readForm slots projected projection upper level hbranch d A s table pair.1)
    (readForm slots projected projection upper level hbranch d A s table pair.2)
    (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection projection
      (HierarchicalLeftDecoder.LowerNode upper level d))))

def rawCollision (s : Nat)
    (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r) : ℝ :=
  (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats path))
    (cutSlots path projected) rows).probability
      (fun raw => collision slots projected projection upper level hbranch d A s table
        (LowerCutPair.arraysPair rows repeats path projected exterior a raw))

theorem fiber_collision_eq (s : Nat)
    (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r)
    (bg : Background path projected a) :
    ((FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)).product
      (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d))).probability
        (ProjectedFiberSquare.restrictedPair slots projected projection upper level hbranch d A
          (ProjectedFiberRawPair.direction path upper level d hnode a)
          (baseline path projected a exterior bg) s table) =
      ((FiniteDistribution.uniform (H (cutSlots path projected))).product
        (FiniteDistribution.uniform (H (cutSlots path projected)))).probability
          (fun pair => collision slots projected projection upper level hbranch d A s table
            (LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior bg pair.1,
              LowerCutFiberDisintegration.arraysAt rows repeats path projected a exterior bg pair.2)) := by
  have hprod := FiniteDistribution.product_pushforward
    (FiniteDistribution.uniform (H (cutSlots path projected)))
    (FiniteDistribution.uniform (H (cutSlots path projected)))
    (ProjectedFiberRawPair.scalar path projected upper level d hnode)
    (ProjectedFiberRawPair.scalar path projected upper level d hnode)
  simp only [ProjectedFiberBackground.scalar_uniform path projected upper level d hnode] at hprod
  rw [← hprod, FiniteDistribution.probability_pushforward]
  apply congrArg (fun event : H (cutSlots path projected) × H (cutSlots path projected) → Bool =>
    ((FiniteDistribution.uniform (H (cutSlots path projected))).product
      (FiniteDistribution.uniform (H (cutSlots path projected)))).probability event)
  funext pair
  unfold ProjectedFiberSquare.restrictedPair baseline collision readForm
  rw [ProjectedFiberBackground.form_at_fiber rows repeats path projected upper level d hnode a
    exterior bg slots projection hbranch A table s pair.1,
    ProjectedFiberBackground.form_at_fiber rows repeats path projected upper level d hnode a
    exterior bg slots projection hbranch A table s pair.2]

theorem rawCollision_eq_mean (s : Nat)
    (table : ProjectedLowerFiber.UpperTable (rows := rows) slots upper level r) :
    rawCollision path slots projected projection upper level hbranch d a exterior A s table =
      (backgroundLaw path projected a).expectation (fun bg =>
        ((FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)).product
          (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d))).probability
            (ProjectedFiberSquare.restrictedPair slots projected projection upper level hbranch d A
              (ProjectedFiberRawPair.direction path upper level d hnode a)
              (baseline path projected a exterior bg) s table)) := by
  unfold rawCollision
  rw [LowerCutFiberDisintegration.probability_pair rows repeats path projected a exterior]
  unfold LowerCutFiberDisintegration.law
  rw [probability_product]
  apply FiniteDistribution.expectation_congr
  intro bg
  exact (fiber_collision_eq path slots projected projection upper level hbranch d hnode a exterior
    A s table bg).symm

variable
  (known : Background path projected a → HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

def meanSuccess (s : Nat) : ℝ :=
  (backgroundLaw path projected a).expectation (fun bg =>
    ProjectedFiberSquare.success slots projected projection upper level hbranch d A
      (ProjectedFiberRawPair.direction path upper level d hnode a)
      (baseline path projected a exterior bg) (known bg) repeats cut σ useful ρ threshold s
      (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)))

theorem meanSuccess_square_le (s : Nat) :
    meanSuccess path slots projected projection upper level hbranch d hnode a exterior A
        known cut σ useful ρ threshold s ^ 2 ≤
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
        (rawCollision path slots projected projection upper level hbranch d a exterior A s) := by
  unfold meanSuccess
  apply (CollisionAveraging.mean_square_le _ _).trans
  calc
    _ ≤ (backgroundLaw path projected a).expectation (fun bg =>
        (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
          (fun table =>
            ((FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)).product
              (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d))).probability
                (ProjectedFiberSquare.restrictedPair slots projected projection upper level hbranch d A
                  (ProjectedFiberRawPair.direction path upper level d hnode a)
                  (baseline path projected a exterior bg) s table))) := by
      apply Finset.sum_le_sum
      intro bg _
      exact mul_le_mul_of_nonneg_left
        (ProjectedFiberUpperSeed.success_square_le_upperSeed slots projected upper level d A
          (ProjectedFiberRawPair.direction path upper level d hnode a)
          (baseline path projected a exterior bg) (known bg) repeats cut σ useful ρ threshold
          projection hbranch s (FiniteDistribution.uniform
            (ProjectedLowerFiber.Scalar projected upper level d)))
        ((backgroundLaw path projected a).nonnegative bg)
    _ = _ := by
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro table
      exact (rawCollision_eq_mean path slots projected projection upper level hbranch d hnode a
        exterior A s table).symm

end
end PerfectCompleteness.LowerProjectedFiberAverage

end

end OAI
