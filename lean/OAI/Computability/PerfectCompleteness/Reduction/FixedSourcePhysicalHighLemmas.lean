import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionPhysicalHigh
import OAI.Computability.PerfectCompleteness.Decoding.SourceQuestionCollisionTransportLemmas
import OAI.Computability.PerfectCompleteness.Decoding.SourceQuestionPhysicalCollision

namespace OAI

section

namespace PerfectCompleteness.FixedSourcePhysicalHigh

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (pDown : Path (branch parameters) (Nodes.height upper) (height + 1))
  (hproper : height + 1 < Nodes.height upper)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode ((Nodes.path upper).append pDown) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper (height + 1) d))
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    ((Nodes.path upper).append pDown) outside placeholder)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
      upper (height + 1) bg → Prop)
  (density threshold : ℝ)

local instance rowSpaceFintype (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper)

local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

def tagLaw : FiniteDistribution
    (SourceProjectedTag.Tag (branch := branch parameters) (n := height)
      (t := sourceLength parameters.plan hδ)) :=
  SourceProjectedTag.law (FixedSourceGlobalCollision.flag parameters)

def success (direction : BucketSampler.Direction (rows parameters.plan (height + 1)))
    (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height))
    (tag : SourceProjectedTag.Tag (branch := branch parameters) (n := height)
      (t := sourceLength parameters.plan hδ)) : ℝ :=
  SourceQuestionPhysicalHigh.success outside placeholder clauses designated q tag.1 tag.2 upper pDown
    hproper (height + 1) (FixedLowerRawCollision.branchPositive parameters) d hnode A cut σ (useful q)
    density threshold exterior direction (cutoff parameters.plan hδ)

def probability : ℝ :=
  (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
    (fun direction => (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
      (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
        (tagLaw parameters).expectation
          (success parameters outside placeholder clauses designated upper pDown hproper d hnode A cut
            exterior σ useful density threshold direction q)))

theorem probability_square_le_collision :
    probability parameters outside placeholder clauses designated upper pDown hproper d hnode A cut
        exterior σ useful density threshold ^ 2 ≤
      (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
        (fun direction => (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            (HierarchicalAllDecoderTables.upperTableLaw
              (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
              upper (height + 1) σ (useful q) adviceRows density).expectation (fun table =>
                (tagLaw parameters).expectation (fun tag =>
                  SourceQuestionPhysicalHigh.collision ((Nodes.path upper).append pDown) outside placeholder
                    clauses designated q tag.1 tag.2 upper (height + 1) d
                    (FixedLowerRawCollision.branchPositive parameters) A exterior direction
                    (cutoff parameters.plan hδ) table)))) := by
  unfold probability
  apply (CollisionAveraging.mean_square_le _ _).trans
  apply SmallBias.expectation_mono
  intro direction
  apply (CollisionAveraging.mean_square_le _ _).trans
  apply SmallBias.expectation_mono
  intro q
  apply (CollisionAveraging.mean_square_le _ _).trans
  rw [FiniteDistribution.expectation_comm]
  apply SmallBias.expectation_mono
  intro tag
  exact SourceQuestionPhysicalHigh.success_square_le outside placeholder clauses designated q tag.1 tag.2
    upper pDown hproper (height + 1) (FixedLowerRawCollision.branchPositive parameters) d hnode A cut
    σ (useful q) density threshold exterior direction (cutoff parameters.plan hδ)

end
end PerfectCompleteness.FixedSourcePhysicalHigh

end

section

namespace PerfectCompleteness.FixedSourceHighBound

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (pDown : Path (branch parameters) (Nodes.height upper) (height + 1))
  (hproper : height + 1 < Nodes.height upper)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode ((Nodes.path upper).append pDown) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper (height + 1) d))
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    ((Nodes.path upper).append pDown) outside placeholder)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
      upper (height + 1) bg → Prop)
  (density threshold : ℝ)

local instance rowSpaceFintype (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  Fintype.ofFinite _

local instance upperAnswerFintype (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper)

local instance directionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩

omit [NeZero m] in
theorem tag_collision_eq
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1)))
    (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height))
    (table : SourceQuestionLowerForms.UpperTable (rows := rows parameters.plan)
      ((Nodes.path upper).append pDown) outside clauses upper (height + 1)
      (adviceRows := adviceRows) q) :
    (FixedSourcePhysicalHigh.tagLaw parameters).expectation (fun tag =>
      SourceQuestionPhysicalHigh.collision ((Nodes.path upper).append pDown) outside placeholder
        clauses designated q tag.1 tag.2 upper (height + 1) d
        (FixedLowerRawCollision.branchPositive parameters) A exterior direction
        (cutoff parameters.plan hδ) table) =
      FixedSourceGlobalCollision.localProbability parameters ((Nodes.path upper).append pDown)
        outside placeholder clauses designated upper d A exterior q table direction := by
  simpa only [FixedSourcePhysicalHigh.tagLaw, SourceProjectedTag.law,
    FiniteDistribution.expectation_product, FixedSourceGlobalCollision.localProbability,
    FixedSourceGlobalCollision.localTables, Function.update_self] using
    (SourceQuestionPhysicalCollision.mean_collision_eq ((Nodes.path upper).append pDown)
      outside placeholder clauses designated upper (height + 1) d
      (FixedLowerRawCollision.branchPositive parameters) A exterior q direction
      (cutoff parameters.plan hδ)
      (FixedSourceGlobalCollision.localTables parameters ((Nodes.path upper).append pDown)
        outside clauses upper q table) (FixedSourceGlobalCollision.flag parameters))

theorem probability_square_le (hdensity : 0 < density) :
    FixedSourcePhysicalHigh.probability parameters outside placeholder clauses designated upper pDown
        hproper d hnode A cut exterior σ useful density threshold ^ 2 ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  have h := FixedSourcePhysicalHigh.probability_square_le_collision parameters outside placeholder
    clauses designated upper pDown hproper d hnode A cut exterior σ useful density threshold
  simp_rw [tag_collision_eq] at h
  exact h.trans (FixedSourceGlobalCollision.mean_local_le parameters ((Nodes.path upper).append pDown)
    outside placeholder clauses designated upper d hnode A exterior σ useful density hdensity)

end
end PerfectCompleteness.FixedSourceHighBound

end

end OAI
