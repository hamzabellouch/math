import OAI.Computability.PerfectCompleteness.Decoding.DecoderTableCoupling
import OAI.Computability.PerfectCompleteness.Decoding.ProjectedLowerFiber
import OAI.Computability.PerfectCompleteness.Decoding.ProjectedNativeCollision
import OAI.Computability.PerfectCompleteness.Foundations.MultiplicationFormInjectiveLemmas

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberSquare

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open ProjectedLowerFiber

attribute [local instance] RightDecoder.scalarFintype

private theorem table_sampling {Q Y Z Ω : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype Y] [Fintype Z] [Fintype Ω]
    (responses : Q → FiniteDistribution Y) (right : FiniteDistribution Z)
    (ν : FiniteDistribution Ω) (question : Ω → Q) (event : Ω → Y × Z → Bool) :
    ν.expectation (fun x => ((responses (question x)).product right).probability (event x)) =
      ((FiniteDistribution.table responses).product right).expectation
        (fun seed => ν.probability (fun x => event x (seed.1 (question x), seed.2))) := by
  simp_rw [DecoderTableCoupling.probability_eq_expectation]
  symm
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro x
  simp only [FiniteDistribution.expectation_product]
  exact FiniteDistribution.expectation_table_eval responses (question x)
    (fun y => right.expectation (fun z => if event x (y, z) then (1 : ℝ) else 0))

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

local instance rowSpaceFintype : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)

def form (s : Nat) (q : HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  (HierarchicalDecoderTables.decode slots upper level hbranch d s q).map
    (OddListExtraction.multiplicationForm
      (HierarchicalDecoderTables.LowerH slots upper level d))

def highMeeting (s : Nat)
    (q : HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (right : Module.Dual F2 (OwnInputReference.UpperSpace projected upper)) : Bool :=
  decide (s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q) ∧
    DecoderSourcePullback.upperTarget projection upper q = right)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Direction (rows := rows) upper level d) (arrays : Arrays projected rows)

def restrictedPair (s : Nat) (table : UpperTable (rows := rows) slots upper level r)
    (pair : Scalar projected upper level d × Scalar projected upper level d) : Bool :=
  BilinearCollisionTransfer.restrictedCollision
    (form slots upper level hbranch d s
      (upperAt slots projected projection upper level d A a arrays table pair.1))
    (form slots upper level hbranch d s
      (upperAt slots projected projection upper level d A a arrays table pair.2))
    (LinearMap.range (HPullback
      (ChildBlockProjection.nodeProjection projection (lower upper level d))))

theorem fixed_seed_square (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d))
    (table : UpperTable (rows := rows) slots upper level r)
    (right : Module.Dual F2 (OwnInputReference.UpperSpace projected upper)) :
    ν.probability (fun fresh => highMeeting slots projected projection upper level hbranch d s
        (upperAt slots projected projection upper level d A a arrays table fresh) right) ^ 2 ≤
      (ν.product ν).probability
        (restrictedPair slots projected projection upper level hbranch d A a arrays s table) := by
  rw [pow_two, ← SingleResponseResampling.probability_rectangle]
  apply FiniteDistribution.probability_mono
  intro pair hpair
  obtain ⟨h0, h1⟩ := Bool.and_eq_true_iff.mp hpair
  obtain ⟨hrank0, hhit0⟩ := of_decide_eq_true h0
  obtain ⟨hrank1, hhit1⟩ := of_decide_eq_true h1
  exact ProjectedNativeCollision.two_high_hits_restricted projection upper level hbranch d s
    (upperAt slots projected projection upper level d A a arrays table pair.1)
    (upperAt slots projected projection upper level d A a arrays table pair.2)
    right hrank0 hrank1 hhit0 hhit1

variable
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper (lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

def rightLaw :=
  RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
    repeats cut σ
    (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
      (LinearMap.ker A) a.val known arrays) threshold

def seedLaw :=
  (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).product
    (rightLaw projected upper level d A a arrays known repeats cut σ threshold)

def success (s : Nat) (ν : FiniteDistribution (Scalar projected upper level d)) : ℝ :=
  ν.expectation (fun fresh =>
    ((HierarchicalAllDecoderTables.upperKernel slots upper level σ useful r ρ
      (inputAt slots projected projection upper level d A a arrays fresh)).product
      (RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
        repeats cut σ
        (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
          (LinearMap.ker A) a.val known (arraysAt projected upper level d a arrays fresh))
        threshold)).probability
      (fun pair => highMeeting slots projected projection upper level hbranch d s pair.1 pair.2))

theorem success_eq_seed_mean (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d)) :
    success slots projected projection upper level hbranch d A a arrays known
        repeats cut σ useful ρ threshold s ν =
      (seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).expectation
        (fun seed => ν.probability (fun fresh =>
          highMeeting slots projected projection upper level hbranch d s
            (upperAt slots projected projection upper level d A a arrays seed.1 fresh) seed.2)) := by
  unfold success
  simp_rw [ProjectedLowerFiber.rightLaw_fixed projected upper level d A a known arrays]
  exact table_sampling
    (HierarchicalAllDecoderTables.upperKernel slots upper level σ useful r ρ)
    (rightLaw projected upper level d A a arrays known repeats cut σ threshold) ν
    (inputAt slots projected projection upper level d A a arrays)
    (fun _ pair => highMeeting slots projected projection upper level hbranch d s pair.1 pair.2)

theorem success_square_le (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d)) :
    success slots projected projection upper level hbranch d A a arrays known
        repeats cut σ useful ρ threshold s ν ^ 2 ≤
      (seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).expectation
        (fun seed => (ν.product ν).probability
          (restrictedPair slots projected projection upper level hbranch d A a arrays s seed.1)) := by
  rw [success_eq_seed_mean]
  apply (CollisionAveraging.mean_square_le _ _).trans
  apply Finset.sum_le_sum
  intro seed _
  exact mul_le_mul_of_nonneg_left
    (fixed_seed_square slots projected projection upper level hbranch d A a arrays
      s ν seed.1 seed.2)
    ((seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).nonnegative seed)

end
end PerfectCompleteness.ProjectedFiberSquare

end

end OAI
