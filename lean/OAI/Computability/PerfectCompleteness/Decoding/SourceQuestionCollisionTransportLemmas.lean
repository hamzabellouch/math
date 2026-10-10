import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionRawSwap
import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionUnmarkedRange
import OAI.Computability.PerfectCompleteness.Decoding.FixedSourceLowerCollision
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutFormCollision

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionCollisionTransport

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (tables : (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m)) →
    SourceQuestionLowerForms.UpperTable (rows := rows) path outside clauses
      upper level (adviceRows := adviceRows) q)
  (cutoff : Nat)

def firstAnswer
    (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m))
    (raw : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q) :
    Option (HierarchicalDecoderTables.Answer
      (SourceQuestionLowerForms.slots path outside clauses q) upper level d) :=
  LowerCutDecoderForm.answer (SourceQuestionLowerForms.slots path outside clauses q)
    upper level d hbranch A (tables q) cutoff
    (LowerCutPair.first rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior)
      (SourceQuestionLowerForms.rawAtCut path outside clauses q raw))

def secondAnswer (direction : BucketSampler.Direction (rows (height + 1)))
    (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m))
    (raw : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q) :
    Option (HierarchicalDecoderTables.Answer
      (SourceQuestionLowerForms.slots path outside clauses q) upper level d) :=
  LowerCutDecoderForm.answer (SourceQuestionLowerForms.slots path outside clauses q)
    upper level d hbranch A (tables q) cutoff
    (LowerCutPair.second rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior)
      direction (SourceQuestionLowerForms.rawAtCut path outside clauses q raw))

variable
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := height) (t := t))
  (raw : (i : Fin (branch height)) →
    SourceChildKernel.Raw (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (t := t) rows clauses designated i)

def projection : ∀ s k, MixedSupport.Projection
    (SourceQuestionLowerForms.slots path outside clauses q s k)
    (CutSlotAssembly.fill path outside
      (SourceChildKernel.parentRightSlots rows clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) raw) s k) :=
  CutProjectionAssembly.fillProjection path outside
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceChildKernel.parentRightSlots rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw)

def globalRestricted (direction : BucketSampler.Direction (rows (height + 1))) : Bool :=
  let record := SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw
  BilinearCollisionTransfer.restrictedCollision
    ((firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      q record.2).map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d)))
    ((secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      direction q record.2).map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d)))
    (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
      (projection path outside clauses designated q choices raw)
      (HierarchicalLeftDecoder.LowerNode upper level d))))

theorem globalRestricted_imp_native
    (hnode : WholeArrayInteriorExterior.upperNode path =
      HierarchicalLeftDecoder.LowerNode upper level d)
    (direction : BucketSampler.Direction (rows (height + 1)))
    (hcollision : globalRestricted path outside placeholder clauses upper level d hbranch A
      exterior tables cutoff designated q choices raw direction = true) :
    BilinearCollisionTransfer.restrictedCollision
      (SourceQuestionLowerForms.first path outside placeholder clauses upper level d hnode hbranch A
        exterior tables cutoff q (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
      (SourceQuestionLowerForms.second path outside placeholder clauses upper level d hnode hbranch A
        exterior tables cutoff direction q
        (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
      (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
        (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).1) = true := by
  have hU : ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
        (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).1 ≤
      LinearMap.range (HPullback
        (SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw)) :=
    SourceQuestionUnmarkedRange.unmarked_le_range rows clauses designated q choices raw
  have h := LowerCutFormCollision.restricted_on_native path outside
    (SourceChildMarkedLaw.questionSlots clauses q) upper level d hnode
    (SourceChildKernel.parentRightSlots rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw)
    (firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      q (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
    (secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      direction q (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
    (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
      (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).1)
    hU hcollision
  have hmapper :
      LowerCutFormCollision.nativeForm path outside (SourceChildMarkedLaw.questionSlots clauses q)
          upper level d hnode =
        (fun answer : HierarchicalDecoderTables.Answer
            (SourceQuestionLowerForms.slots path outside clauses q) upper level d =>
          CutNativeForms.formCast (SourceQuestionLowerForms.cutSlots_eq path outside clauses q)
            (LowerCutDecoderForm.form path (SourceQuestionLowerForms.slots path outside clauses q)
              upper level d hnode answer)) := by
    funext answer
    rfl
  have hfirst (record : SourceQuestionLowerForms.Raw
      (rows := rows) (repeats := repeats) path clauses q) :
      SourceQuestionLowerForms.first path outside placeholder clauses upper level d hnode hbranch A
          exterior tables cutoff q record =
        (firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
          q record).map (LowerCutFormCollision.nativeForm path outside
            (SourceChildMarkedLaw.questionSlots clauses q) upper level d hnode) := by
    change ((firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables
      cutoff q record).map
        (LowerCutDecoderForm.form path (SourceQuestionLowerForms.slots path outside clauses q)
          upper level d hnode)).map
        (CutNativeForms.formCast (SourceQuestionLowerForms.cutSlots_eq path outside clauses q)) = _
    rw [Option.map_map]
    exact congrArg (fun mapper => (firstAnswer path outside placeholder clauses upper level d
      hbranch A exterior tables cutoff q record).map mapper) hmapper.symm
  have hsecond (record : SourceQuestionLowerForms.Raw
      (rows := rows) (repeats := repeats) path clauses q) :
      SourceQuestionLowerForms.second path outside placeholder clauses upper level d hnode hbranch A
          exterior tables cutoff direction q record =
        (secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
          direction q record).map (LowerCutFormCollision.nativeForm path outside
            (SourceChildMarkedLaw.questionSlots clauses q) upper level d hnode) := by
    change ((secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables
      cutoff direction q record).map
        (LowerCutDecoderForm.form path (SourceQuestionLowerForms.slots path outside clauses q)
          upper level d hnode)).map
        (CutNativeForms.formCast (SourceQuestionLowerForms.cutSlots_eq path outside clauses q)) = _
    rw [Option.map_map]
    exact congrArg (fun mapper => (secondAnswer path outside placeholder clauses upper level d
      hbranch A exterior tables cutoff direction q record).map mapper) hmapper.symm
  rw [hfirst, hsecond]
  exact h

end
end PerfectCompleteness.SourceQuestionCollisionTransport

end

section

namespace PerfectCompleteness.FixedSourceGlobalCollision

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

def flag : Fin (branch parameters height) → FiniteDistribution Bool :=
  fun _ => ProjectionPosterior.bernoulli (projectionProbability parameters height : ℝ)
    (by exact_mod_cast (projectionProbability_bounds parameters height).1.le)
    (by exact_mod_cast (projectionProbability_bounds parameters height).2.le)

abbrev Choice := SourceQuestionKernelJoint.ChoiceTuple
  (branch := branch parameters) (n := height) (t := sourceLength parameters.plan hδ)

def nativeProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
    (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
      (SourceProjectedTag.positionLaw (branch := branch parameters) (n := height)
        (t := sourceLength parameters.plan hδ)).expectation (fun choices =>
          (SourceQuestionRawSwap.kernelLaw
            (C := FixedSourceChildCollision.Calls parameters path)
            (rows parameters.plan) clauses designated (flag parameters) q choices).probability (fun raw =>
              let record := SourceChildMarkedLaw.markedBlocks
                (rows parameters.plan) clauses designated q choices raw
              BilinearCollisionTransfer.restrictedCollision
                (FixedSourceLowerCollision.first parameters path outside placeholder clauses
                  upper d hnode A exterior tables q record.2)
                (FixedSourceLowerCollision.second parameters path outside placeholder clauses
                  upper d hnode A exterior tables direction q record.2)
                (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q) record.1))))

theorem nativeProbability_eq_marked
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :
    nativeProbability parameters path outside placeholder clauses designated upper d hnode A
        exterior tables direction =
      FixedSourceLowerCollision.markedProbability parameters path outside placeholder clauses
        designated upper d hnode A exterior tables direction := by
  let event (q : Questions (m := m) parameters (height := height))
      (choices : Choice parameters (height := height))
      (raw : SourceChildKernelJoint.RawTuple
        (C := FixedSourceChildCollision.Calls parameters path)
        (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated) : Bool :=
    let record := SourceChildMarkedLaw.markedBlocks
      (rows parameters.plan) clauses designated q choices raw
    BilinearCollisionTransfer.restrictedCollision
      (FixedSourceLowerCollision.first parameters path outside placeholder clauses
        upper d hnode A exterior tables q record.2)
      (FixedSourceLowerCollision.second parameters path outside placeholder clauses
        upper d hnode A exterior tables direction q record.2)
      (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q) record.1)
  have hlaw : FixedSourceChildCollision.markedLaw parameters path clauses designated =
      SourceChildKernel.originalLaw
        (C := FixedSourceChildCollision.Calls parameters path)
        (t := sourceLength parameters.plan hδ)
        (rows parameters.plan) clauses designated (flag parameters) := rfl
  have hevent : FixedSourceChildCollision.restrictedEvent parameters path clauses designated
      (FixedSourceLowerCollision.first parameters path outside placeholder clauses
        upper d hnode A exterior tables)
      (FixedSourceLowerCollision.second parameters path outside placeholder clauses
        upper d hnode A exterior tables direction) =
      (fun sample => event
        (SourceQuestionRawSwap.insideQuestions (rows parameters.plan) clauses designated sample)
        (SourceQuestionRawSwap.positions (rows parameters.plan) clauses designated sample)
        (SourceQuestionRawSwap.raw (rows parameters.plan) clauses designated sample)) := by
    funext sample
    rfl
  unfold nativeProbability FixedSourceLowerCollision.markedProbability
  rw [hlaw, hevent]
  simp_rw [DecoderTableCoupling.probability_eq_expectation]
  exact (SourceQuestionRawSwap.originalLaw_expectation
    (C := FixedSourceChildCollision.Calls parameters path)
    (rows parameters.plan) clauses designated (flag parameters)
    (fun q choices raw => if event q choices raw then 1 else 0)).symm

def globalProbability
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
    (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
      (SourceProjectedTag.positionLaw (branch := branch parameters) (n := height)
        (t := sourceLength parameters.plan hδ)).expectation (fun choices =>
          (SourceQuestionRawSwap.kernelLaw
            (C := FixedSourceChildCollision.Calls parameters path)
            (rows parameters.plan) clauses designated (flag parameters) q choices).probability
              (fun raw => SourceQuestionCollisionTransport.globalRestricted path outside placeholder
                clauses upper (height + 1) d (FixedLowerRawCollision.branchPositive parameters)
                A exterior tables (cutoff parameters.plan hδ) designated q choices raw direction)))

theorem globalProbability_le_marked
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :
    globalProbability parameters path outside placeholder clauses designated upper d A
        exterior tables direction ≤
      FixedSourceLowerCollision.markedProbability parameters path outside placeholder clauses
        designated upper d hnode A exterior tables direction := by
  rw [← nativeProbability_eq_marked]
  apply SmallBias.expectation_mono
  intro q
  apply SmallBias.expectation_mono
  intro choices
  apply FiniteDistribution.probability_mono
  intro raw hcollision
  exact SourceQuestionCollisionTransport.globalRestricted_imp_native path outside placeholder clauses
    upper (height + 1) d (FixedLowerRawCollision.branchPositive parameters) A exterior tables
    (cutoff parameters.plan hδ) designated q choices raw hnode direction hcollision

def localTables (q : Questions (m := m) parameters (height := height))
    (table : Table parameters path outside clauses upper (adviceRows := adviceRows) q) :
    TableFamily parameters path outside clauses upper (adviceRows := adviceRows) :=
  Function.update (fun _ => fun _ => 0) q table

def localProbability (q : Questions (m := m) parameters (height := height))
    (table : Table parameters path outside clauses upper (adviceRows := adviceRows) q)
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) : ℝ :=
  (SourceProjectedTag.positionLaw (branch := branch parameters) (n := height)
    (t := sourceLength parameters.plan hδ)).expectation (fun choices =>
      (SourceQuestionRawSwap.kernelLaw
        (C := FixedSourceChildCollision.Calls parameters path)
        (rows parameters.plan) clauses designated (flag parameters) q choices).probability
          (fun raw => SourceQuestionCollisionTransport.globalRestricted path outside placeholder
            clauses upper (height + 1) d (FixedLowerRawCollision.branchPositive parameters)
            A exterior (localTables parameters path outside clauses upper q table)
            (cutoff parameters.plan hδ) designated q choices raw direction))

theorem globalProbability_eq_local
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :
    globalProbability parameters path outside placeholder clauses designated upper d A
        exterior tables direction =
      (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
        (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
          localProbability parameters path outside placeholder clauses designated upper d A
            exterior q (tables q) direction) := by
  simp only [globalProbability, localProbability, SourceQuestionCollisionTransport.globalRestricted,
    SourceQuestionCollisionTransport.firstAnswer, SourceQuestionCollisionTransport.secondAnswer,
    localTables, Function.update_self]

variable
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots path outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) bg → Prop)
  (density : ℝ)

include hnode in
theorem mean_global_le (hdensity : 0 < density) :
    (FixedSourceLowerCollision.tableLaw parameters path outside clauses upper σ useful density).expectation
      (fun tables => (FiniteDistribution.uniform
        (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
          (globalProbability parameters path outside placeholder clauses designated upper d A
            exterior tables)) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  apply le_trans _ (FixedSourceLowerCollision.mean_marked_le parameters path outside placeholder clauses
    designated upper d hnode A exterior σ useful density hdensity)
  apply SmallBias.expectation_mono
  intro tables
  apply SmallBias.expectation_mono
  intro direction
  exact globalProbability_le_marked parameters path outside placeholder clauses designated upper d hnode A
    exterior tables direction

include hnode in

theorem mean_local_le (hdensity : 0 < density) :
    (FiniteDistribution.uniform
      (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation (fun direction =>
        (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            (HierarchicalAllDecoderTables.upperTableLaw
              (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
              σ (useful q) adviceRows density).expectation (fun table =>
                localProbability parameters path outside placeholder clauses designated upper d A
                  exterior q table direction))) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  have h := mean_global_le parameters path outside placeholder clauses designated upper d hnode A exterior
    σ useful density hdensity
  have hglobal : ∀ tables : TableFamily parameters path outside clauses upper
        (adviceRows := adviceRows),
      globalProbability parameters path outside placeholder clauses designated upper d A
          exterior tables =
        fun direction => (PreliminarySampler.questionsLaw
          (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            localProbability parameters path outside placeholder clauses designated upper d A
              exterior q (tables q) direction) := by
    intro tables
    funext direction
    exact globalProbability_eq_local parameters path outside placeholder clauses designated upper d A
      exterior tables direction
  simp_rw [hglobal] at h
  rw [FiniteDistribution.expectation_comm] at h
  convert h using 1
  apply FiniteDistribution.expectation_congr
  intro direction
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro q
  exact (FiniteProduct.expectation_eval
    (fun q => HierarchicalAllDecoderTables.upperTableLaw
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
      σ (useful q) adviceRows density) q
    (fun table => localProbability parameters path outside placeholder clauses designated upper d A
      exterior q table direction)).symm

end
end PerfectCompleteness.FixedSourceGlobalCollision

end

end OAI
