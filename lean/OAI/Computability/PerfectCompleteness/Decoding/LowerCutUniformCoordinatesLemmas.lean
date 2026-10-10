import OAI.Computability.PerfectCompleteness.Algebra.FixedRankContradiction
import OAI.Computability.PerfectCompleteness.Decoding.FixedLowerUniformCollision
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairLemmas
import OAI.Computability.PerfectCompleteness.Machines.LowerCutInstalledInput
import OAI.Computability.PerfectCompleteness.Reduction.PreliminaryAveraging

namespace OAI

section

namespace PerfectCompleteness.LowerCutUniformCoordinates

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}
  (rows : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

abbrev NativeSample :=
  BucketSampler.Direction (rows (m + 1)) ×
    (LowerCutPair.NativeMatrix rows p slots × H (WholeCutGrouping.cutSlots p slots))

abbrev LowerSample :=
  BucketSampler.Direction
      (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) ×
    (HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d ×
      HierarchicalDecoderTables.LowerH slots upper lowerLevel d)

def sampleEquiv : NativeSample rows p slots ≃ LowerSample rows slots upper lowerLevel d :=
  (LowerCutInstalledInput.lowerDirectionEquiv rows p upper lowerLevel d hnode).prodCongr
    ((LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode).toEquiv.prodCongr
      (LowerCutInstalledInput.lowerScalarEquiv p slots upper lowerLevel d hnode).toEquiv)

@[simp] theorem sampleEquiv_apply (x : NativeSample rows p slots) :
    sampleEquiv rows p slots upper lowerLevel d hnode x =
      (LowerCutInstalledInput.lowerDirectionEquiv rows p upper lowerLevel d hnode x.1,
        (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode x.2.1,
          LowerCutInstalledInput.lowerScalarEquiv p slots upper lowerLevel d hnode x.2.2)) := rfl

variable [Nonempty (BucketSampler.Direction (rows (m + 1)))]

include p hnode in

theorem lowerDirection_nonempty :
    Nonempty (BucketSampler.Direction
      (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))) := by
  obtain ⟨a⟩ := (inferInstance : Nonempty (BucketSampler.Direction (rows (m + 1))))
  exact ⟨LowerCutInstalledInput.lowerDirectionEquiv rows p upper lowerLevel d hnode a⟩

local instance lowerHFintype :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _

theorem uniformLaw_pushforward :
    letI := lowerDirection_nonempty rows p upper lowerLevel d hnode
    (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))).pushforward (sampleEquiv rows p slots upper lowerLevel d hnode) =
      FixedLowerUniformCollision.uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) := by
  let := lowerDirection_nonempty rows p upper lowerLevel d hnode
  have h := UniformConditioning.uniform_transport (sampleEquiv rows p slots upper lowerLevel d hnode)
  rw [FiniteDistribution.transport_eq_pushforward] at h
  simpa only [FixedLowerUniformCollision.uniformLaw, WholeCutSampler.uniform_product] using h

theorem probability_transport (event : LowerSample rows slots upper lowerLevel d → Bool) :
    letI := lowerDirection_nonempty rows p upper lowerLevel d hnode
    (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))).probability
        (fun x => event (sampleEquiv rows p slots upper lowerLevel d hnode x)) =
      (FixedLowerUniformCollision.uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability event := by
  let := lowerDirection_nonempty rows p upper lowerLevel d hnode
  have h := congrArg
    (fun μ : FiniteDistribution (LowerSample rows slots upper lowerLevel d) => μ.probability event)
    (uniformLaw_pushforward rows p slots upper lowerLevel d hnode)
  rw [FiniteDistribution.probability_pushforward] at h
  exact h

theorem expectation_transport (f : LowerSample rows slots upper lowerLevel d → ℝ) :
    letI := lowerDirection_nonempty rows p upper lowerLevel d hnode
    (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))).expectation
        (fun x => f (sampleEquiv rows p slots upper lowerLevel d hnode x)) =
      (FixedLowerUniformCollision.uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).expectation f := by
  let := lowerDirection_nonempty rows p upper lowerLevel d hnode
  have h := congrArg
    (fun μ : FiniteDistribution (LowerSample rows slots upper lowerLevel d) => μ.expectation f)
    (uniformLaw_pushforward rows p slots upper lowerLevel d hnode)
  rw [FiniteDistribution.expectation_pushforward] at h
  exact h

variable {Y : Type*} [Fintype Y]

omit [Nonempty (BucketSampler.Direction (rows (m + 1)))] [Fintype Y] in
theorem collision_transport
    (f : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d → Option Y)
    (x : NativeSample rows p slots) :
    FixedLowerUniformCollision.uniformCollision (H (WholeCutGrouping.cutSlots p slots))
        (rows (m + 1))
        (fun X => f (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode X)) x =
      FixedLowerUniformCollision.uniformCollision
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) f
        (sampleEquiv rows p slots upper lowerLevel d hnode x) := by
  exact congrArg
    (fun X => TwoResponseCollision.collision f
      (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode x.2.1, X))
    (LowerCutInstalledInput.shift_lowerMatrixEquiv rows p slots upper lowerLevel d hnode
      x.2.1 x.1 x.2.2)

omit [Fintype Y] in
theorem collision_probability
    (f : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d → Option Y) :
    letI := lowerDirection_nonempty rows p upper lowerLevel d hnode
    (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))).probability
        (FixedLowerUniformCollision.uniformCollision (H (WholeCutGrouping.cutSlots p slots))
          (rows (m + 1))
          (fun X => f (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode X))) =
      (FixedLowerUniformCollision.uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability
          (FixedLowerUniformCollision.uniformCollision
            (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
            (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) f) := by
  let := lowerDirection_nonempty rows p upper lowerLevel d hnode
  have hevent := funext (collision_transport rows p slots upper lowerLevel d hnode f)
  rw [hevent]
  exact probability_transport rows p slots upper lowerLevel d hnode _

end
end PerfectCompleteness.LowerCutUniformCoordinates

end

section

namespace PerfectCompleteness.LowerCutUniformCollisionLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

theorem direction_probability_eq {Y : Type*} [Fintype Y]
    (answer : Arrays slots rows → Option Y)
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (WholeCutGrouping.cutSlots p slots) rows).probability
        (fun raw => TwoResponseCollision.collision answer
          (LowerCutPair.arraysPair rows repeats p slots exterior a raw)) =
      (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats p slots)).expectation
        (fun c => ((FiniteDistribution.uniform (LowerCutPair.NativeMatrix rows p slots)).product
          (FiniteDistribution.uniform (H (WholeCutGrouping.cutSlots p slots)))).probability
            (fun z => TwoResponseCollision.collision
              (fun X => answer (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X))
              (z.1, EvaluationMatrix.shift (H (WholeCutGrouping.cutSlots p slots)) z.1 a.val z.2))) := by
  have h := congrArg
    (fun μ : FiniteDistribution (Arrays slots rows × Arrays slots rows) =>
      μ.probability (TwoResponseCollision.collision answer))
    (LowerCutPairBackground.arraysPair_law rows repeats p slots exterior a)
  simp only [FiniteDistribution.probability_pushforward] at h
  rw [PreliminaryAveraging.probability_product] at h
  simp only [FiniteDistribution.probability_pushforward] at h
  exact h

theorem native_probability_eq {Y : Type*} [Fintype Y]
    [Nonempty (BucketSampler.Direction (rows (m + 1)))]
    (answer : Arrays slots rows → Option Y)
    (exterior : WholeCutGrouping.Exterior rows repeats p slots) :
    (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).expectation
      (fun a => (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
        (WholeCutGrouping.cutSlots p slots) rows).probability
          (fun raw => TwoResponseCollision.collision answer
            (LowerCutPair.arraysPair rows repeats p slots exterior a raw))) =
      (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats p slots)).expectation
        (fun c => (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
          (rows (m + 1))).probability
            (FixedLowerUniformCollision.uniformCollision _ _
              (fun X => answer (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X)))) := by
  simp_rw [direction_probability_eq rows repeats p slots answer exterior]
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro c
  exact (PreliminaryAveraging.probability_product
    (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1))))
    ((FiniteDistribution.uniform (LowerCutPair.NativeMatrix rows p slots)).product
      (FiniteDistribution.uniform (H (WholeCutGrouping.cutSlots p slots))))
    (FixedLowerUniformCollision.uniformCollision (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))
      (fun X => answer (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X)))).symm

variable (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)
  (hbranch : ∀ k < n, 0 < branch k) {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (table : HierarchicalAllDecoderTables.Input (rows := rows)
    slots upper lowerLevel adviceRows → HierarchicalAllDecoderTables.UpperAnswer slots upper)
  (cutoff : Nat)

local instance lowerHFintype :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _
local instance answerFintype :
    Fintype (HierarchicalDecoderTables.Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype (V := PointwiseSpaces.squareSpace
    (HierarchicalDecoderTables.LowerH slots upper lowerLevel d))

theorem answer_installMatrix
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (c : LowerCutPairBackground.Complement rows repeats p slots)
    (X : LowerCutPair.NativeMatrix rows p slots) :
    LowerCutDecoderForm.answer slots upper lowerLevel d hbranch A table cutoff
        (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X) =
      HierarchicalLowerInverse.matrixTable slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper
          (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
        (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
        A (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d cutoff table)
        (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode X) := by
  exact congrArg
    (fun input : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel adviceRows =>
      HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d cutoff (table input))
    (LowerCutInstalledInput.actualInput_installMatrix rows p slots upper lowerLevel d hnode
      repeats exterior c A X)

include hnode in

theorem probability_eq
    [Nonempty (BucketSampler.Direction (rows (m + 1)))]
    [Nonempty (BucketSampler.Direction
      (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))))]
    (exterior : WholeCutGrouping.Exterior rows repeats p slots) :
    (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).expectation
      (fun a => (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
        (WholeCutGrouping.cutSlots p slots) rows).probability
          (fun raw => TwoResponseCollision.collision
            (LowerCutDecoderForm.answer slots upper lowerLevel d hbranch A table cutoff)
            (LowerCutPair.arraysPair rows repeats p slots exterior a raw))) =
      (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats p slots)).expectation
        (fun c => (FixedLowerUniformCollision.uniformLaw
          (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
          (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability
            (FixedLowerUniformCollision.uniformCollision _ _
              (HierarchicalLowerInverse.matrixTable slots upper lowerLevel
                (HierarchicalMatrixTable.backgroundOf slots upper
                  (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
                (NodeEmbedding.matrix
                  (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
                A (HierarchicalAllDecoderTables.decodeTable
                  slots upper lowerLevel hbranch adviceRows d cutoff table)))) := by
  rw [native_probability_eq rows repeats p slots]
  apply FiniteDistribution.expectation_congr
  intro c
  have h := LowerCutUniformCoordinates.collision_probability rows p slots upper lowerLevel d hnode
    (HierarchicalLowerInverse.matrixTable slots upper lowerLevel
      (HierarchicalMatrixTable.backgroundOf slots upper
        (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
      (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
      A (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d cutoff table))
  have hf := funext
    (answer_installMatrix rows repeats p slots upper lowerLevel d hnode hbranch A table cutoff exterior c)
  rw [hf]
  exact h

end
end PerfectCompleteness.LowerCutUniformCollisionLaw

end

section

namespace PerfectCompleteness.FixedLowerRawCollision

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height t : Nat}
  (path : Path (branch parameters) parameters.plan.depth (height + 1))
  (slots : Slots (branch parameters) parameters.plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)

local instance cutDirectionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

local instance lowerDirectionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan
      (Nodes.height (HierarchicalLeftDecoder.LowerNode upper (height + 1) d)))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth -
      Nodes.height (HierarchicalLeftDecoder.LowerNode upper (height + 1) d)))⟩⟩

local instance lowerHFintype :
    Fintype (HierarchicalDecoderTables.LowerH slots upper (height + 1) d) :=
  Fintype.ofFinite _

local instance upperDualFintype :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper

theorem branchPositive : ∀ k < parameters.plan.depth, 0 < branch parameters k :=
  fun k _ => branch_pos parameters k

variable {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (exterior : WholeCutGrouping.Exterior (rows parameters.plan) (repeats parameters.plan) path slots)

abbrev UpperTable :=
  HierarchicalAllDecoderTables.Input (rows := rows parameters.plan)
    slots upper (height + 1) adviceRows →
      HierarchicalAllDecoderTables.UpperAnswer slots upper

def fullCollisionProbability (table : UpperTable parameters slots upper (height := height)
    (adviceRows := adviceRows)) : ℝ :=
  (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
    (fun direction =>
      (CutChildGrouping.rawLaw
        (C := Option (WholeCutCalls.Index (rows parameters.plan) (repeats parameters.plan) path))
        (WholeCutGrouping.cutSlots path slots) (rows parameters.plan)).probability
          (fun raw => BilinearCollisionTransfer.fullCollision
            (LowerCutDecoderForm.first path slots upper (height + 1) d hnode
              (branchPositive parameters) A table (cutoff parameters.plan hδ) exterior raw)
            (LowerCutDecoderForm.second path slots upper (height + 1) d hnode
              (branchPositive parameters) A table (cutoff parameters.plan hδ) exterior direction raw)))

variable
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper (height + 1) bg → Prop)
  (density : ℝ) (hdensity : 0 < density)

include σ useful density hdensity

theorem supported_fullCollision_le
    (table : UpperTable parameters slots upper (height := height) (adviceRows := adviceRows))
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper (height + 1)
      σ useful adviceRows density).weight table ≠ 0) :
    fullCollisionProbability parameters path slots upper d hnode A exterior table ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 := by
  unfold fullCollisionProbability
  simp_rw [LowerCutDecoderForm.fullCollision_pair]
  rw [LowerCutUniformCollisionLaw.probability_eq
    (rows parameters.plan) (repeats parameters.plan) path slots upper (height + 1) d hnode
    (branchPositive parameters) A table (cutoff parameters.plan hδ) exterior]
  apply (SmallBias.expectation_mono _ (fun c =>
    (FixedLowerUniformCollision.supported_collision_lt parameters.plan hδ slots upper (height + 1)
      (HierarchicalMatrixTable.backgroundOf slots upper
        (LowerCutPairBackground.backgroundArrays (rows parameters.plan) (repeats parameters.plan)
          path slots exterior c))
      (branchPositive parameters) σ useful density hdensity d
      (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays
        (rows parameters.plan) (repeats parameters.plan) path slots exterior c) upper)
      A table hsupport).le)).trans
  exact le_of_eq (SmallBias.expectation_const _ _)

theorem mean_fullCollision_le :
    (HierarchicalAllDecoderTables.upperTableLaw slots upper (height + 1) σ useful
      adviceRows density).expectation
        (fullCollisionProbability parameters path slots upper d hnode A exterior) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 := by
  apply DecoderTableAdmissibility.expectation_le_of_support
  intro table hsupport
  exact supported_fullCollision_le parameters path slots upper d hnode A exterior
    σ useful density hdensity table hsupport

end
end PerfectCompleteness.FixedLowerRawCollision

end

end OAI
