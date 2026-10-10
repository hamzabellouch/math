import OAI.Computability.PerfectCompleteness.Decoding.FixedSourceChildCollision
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutScalarProjectionLemmas
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutUniformCoordinatesLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedSourceLowerCollision

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (path : Path (branch parameters) parameters.plan.depth (height + 1))
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    path outside placeholder)

abbrev Questions := FixedSourceChildCollision.Questions
  (m := m) parameters (height := height)

abbrev Table (q : Questions (m := m) parameters (height := height)) :=
  SourceQuestionLowerForms.UpperTable (rows := rows parameters.plan)
    path outside clauses upper (height + 1) (adviceRows := adviceRows) q

local instance rowSpaceFintype (q : Questions (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype (q : Questions (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper)

local instance tableFintype (q : Questions (m := m) parameters (height := height)) :
    Fintype (Table parameters path outside clauses upper (adviceRows := adviceRows) q) :=
  inferInstanceAs (Fintype (HierarchicalAllDecoderTables.Input (rows := rows parameters.plan)
    (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) adviceRows →
    HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots path outside clauses q) upper))

abbrev TableFamily := (q : Questions (m := m) parameters (height := height)) →
  Table parameters path outside clauses upper (adviceRows := adviceRows) q

local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

def first (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows)) :=
  SourceQuestionLowerForms.first path outside placeholder clauses upper (height + 1) d hnode
    (FixedLowerRawCollision.branchPositive parameters) A exterior tables (cutoff parameters.plan hδ)

def second (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  SourceQuestionLowerForms.second path outside placeholder clauses upper (height + 1) d hnode
    (FixedLowerRawCollision.branchPositive parameters) A exterior tables (cutoff parameters.plan hδ)
    direction

def markedProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (FixedSourceChildCollision.markedLaw parameters path clauses designated).probability
    (FixedSourceChildCollision.restrictedEvent parameters path clauses designated
      (first parameters path outside placeholder clauses upper d hnode A exterior tables)
      (second parameters path outside placeholder clauses upper d hnode A exterior tables direction))

def uniformProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (FixedSourceChildCollision.uniformLaw parameters path clauses).probability
    (FixedSourceChildCollision.fullEvent parameters path clauses
      (first parameters path outside placeholder clauses upper d hnode A exterior tables)
      (second parameters path outside placeholder clauses upper d hnode A exterior tables direction))

variable
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots path outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) bg → Prop)
  (density : ℝ)

def tableLaw : FiniteDistribution
    (TableFamily parameters path outside clauses upper (adviceRows := adviceRows)) :=
  FiniteProduct.law (fun q => HierarchicalAllDecoderTables.upperTableLaw
    (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
    σ (useful q) adviceRows density)

omit [NeZero m] in
private theorem supported_row
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (hsupport : (tableLaw parameters path outside clauses upper σ useful density).weight tables ≠ 0)
    (q : Questions (m := m) parameters (height := height)) :
    (HierarchicalAllDecoderTables.upperTableLaw
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
      σ (useful q) adviceRows density).weight (tables q) ≠ 0 := by
  intro hz
  apply hsupport
  exact Finset.prod_eq_zero (Finset.mem_univ q) hz

theorem supported_uniform_le (hdensity : 0 < density)
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (hsupport : (tableLaw parameters path outside clauses upper σ useful density).weight tables ≠ 0) :
    (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
      (uniformProbability parameters path outside placeholder clauses upper d hnode A exterior tables) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 := by
  have hprob :
      uniformProbability parameters path outside placeholder clauses upper d hnode A exterior tables =
        fun direction => (PreliminarySampler.questionsLaw
          (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            (CutChildGrouping.rawLaw (C := FixedSourceChildCollision.Calls parameters path)
              (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan)).probability
                (fun raw => BilinearCollisionTransfer.fullCollision
                  (first parameters path outside placeholder clauses upper d hnode A exterior tables q raw)
                  (second parameters path outside placeholder clauses upper d hnode A exterior tables
                    direction q raw))) := by
    funext direction
    exact CompletionSoundness.sigmaLaw_probability _ _ _
  rw [hprob, FiniteDistribution.expectation_comm]
  calc
    _ ≤ (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
        (t := sourceLength parameters.plan hδ) (m := m)).expectation
          (fun _ => FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8) := by
      apply SmallBias.expectation_mono
      intro q
      have heq :
          (FiniteDistribution.uniform (BucketSampler.Direction
            (rows parameters.plan (height + 1)))).expectation
            (fun direction => (CutChildGrouping.rawLaw
              (C := FixedSourceChildCollision.Calls parameters path)
              (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan)).probability
                (fun raw => BilinearCollisionTransfer.fullCollision
                  (first parameters path outside placeholder clauses upper d hnode A exterior tables q raw)
                  (second parameters path outside placeholder clauses upper d hnode A exterior tables
                    direction q raw))) =
            FixedLowerRawCollision.fullCollisionProbability parameters path
              (SourceQuestionLowerForms.slots path outside clauses q) upper d hnode A
              (CleanPhysicalReplay.exteriorAt (rows parameters.plan) (repeats parameters.plan)
                path outside placeholder (SourceChildMarkedLaw.questionSlots clauses q) exterior)
              (tables q) := by
        apply FiniteDistribution.expectation_congr
        intro direction
        exact SourceQuestionLowerForms.fullCollision_probability path outside placeholder clauses upper
          (height + 1) d hnode (FixedLowerRawCollision.branchPositive parameters) A exterior tables
          (cutoff parameters.plan hδ) direction q
      rw [heq]
      exact FixedLowerRawCollision.supported_fullCollision_le parameters path
        (SourceQuestionLowerForms.slots path outside clauses q) upper d hnode A
        (CleanPhysicalReplay.exteriorAt (rows parameters.plan) (repeats parameters.plan)
          path outside placeholder (SourceChildMarkedLaw.questionSlots clauses q) exterior)
        σ (useful q) density hdensity (tables q)
        (supported_row parameters path outside clauses upper σ useful density tables hsupport q)
    _ = _ := SmallBias.expectation_const _ _

private theorem expectation_add_const {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (f : X → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x + c) = μ.expectation f + c := by
  simp only [FiniteDistribution.expectation, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, μ.normalized, one_mul]

theorem mean_marked_le (hdensity : 0 < density) :
    (tableLaw parameters path outside clauses upper σ useful density).expectation
      (fun tables => (FiniteDistribution.uniform
        (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
          (markedProbability parameters path outside placeholder clauses designated upper d hnode
            A exterior tables)) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  apply DecoderTableAdmissibility.expectation_le_of_support
  intro tables hsupport
  have hpoint : ∀ direction : BucketSampler.Direction (rows parameters.plan (height + 1)),
      markedProbability parameters path outside placeholder clauses designated upper d hnode
          A exterior tables direction ≤
        uniformProbability parameters path outside placeholder clauses upper d hnode
          A exterior tables direction + 2 * parameters.accuracy := by
    intro direction
    exact FixedSourceChildCollision.restricted_probability_le parameters path clauses designated
      (first parameters path outside placeholder clauses upper d hnode A exterior tables)
      (second parameters path outside placeholder clauses upper d hnode A exterior tables direction)
      le_rfl
  have hmean := SmallBias.expectation_mono
    (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))) hpoint
  rw [expectation_add_const] at hmean
  have huniform := supported_uniform_le parameters path outside placeholder clauses upper d hnode A exterior
    σ useful density hdensity tables hsupport
  linarith

end
end PerfectCompleteness.FixedSourceLowerCollision

end

end OAI
