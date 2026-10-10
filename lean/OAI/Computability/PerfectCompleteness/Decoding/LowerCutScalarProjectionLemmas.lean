import OAI.Computability.PerfectCompleteness.Decoding.CutProjectionAssembly
import OAI.Computability.PerfectCompleteness.Decoding.LowerCutPairLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CutNativeForms
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalReplay
import OAI.Computability.PerfectCompleteness.Sampling.SourceChildMarkedLaw

namespace OAI

section

namespace PerfectCompleteness.LowerCutScalarProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem scalarEquiv_HPullback :
    {n m : Nat} → (p : Path branch n (m + 1)) →
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot) →
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) →
    (f : H (subtreeSlots p projected)) →
    LowerCutNodeCoordinates.scalarEquiv p slots
        (HPullback (fun s k => q (p.slotEmbedding s) k) f) =
      HPullback (ChildBlockProjection.nodeProjection q (upperNode p))
        (LowerCutNodeCoordinates.scalarEquiv p projected f)
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .step i p, slots, projected, q, f =>
      scalarEquiv_HPullback p (childSlots slots i) (childSlots projected i)
        (fun s k => q (i, s) k) f

theorem projectionCast_apply
    {a b c d : Slots branch m → Fin t → MixedSupport.Slot}
    (hab : a = b) (hcd : c = d)
    (q : ∀ s k, MixedSupport.Projection (a s k) (c s k))
    (s : Slots branch m) (k : Fin t) :
    CutNativeForms.projectionCast hab hcd q s k =
      CutProjectionAssembly.castProjection
        (congrFun (congrFun hab s) k) (congrFun (congrFun hcd s) k) (q s k) := by
  cases hab
  cases hcd
  rfl

theorem projectionCast_fill (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) :
    CutNativeForms.projectionCast
        (CleanPhysicalReplay.cutSlots_fill p outside left)
        (CleanPhysicalReplay.cutSlots_fill p outside right)
        (fun s k => CutProjectionAssembly.fillProjection p outside left right q
          (p.slotEmbedding s) k) = q := by
  funext s k
  rw [projectionCast_apply]
  exact CutProjectionAssembly.fillProjection_at_cut_cast p outside left right q s k

theorem inverse_spaceCast_HPullback
    {a b c d : Slots branch m → Fin t → MixedSupport.Slot}
    (hab : a = b) (hcd : c = d)
    (q : ∀ s k, MixedSupport.Projection (a s k) (c s k)) (f : H d) :
    CutNativeForms.spaceCast hab.symm
        (HPullback (CutNativeForms.projectionCast hab hcd q) f) =
      HPullback q (CutNativeForms.spaceCast hcd.symm f) := by
  cases hab
  cases hcd
  rfl

theorem fill_spaceCast_HPullback (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) (f : H right) :
    CutNativeForms.spaceCast (CleanPhysicalReplay.cutSlots_fill p outside left).symm
        (HPullback q f) =
      HPullback
        (fun s k => CutProjectionAssembly.fillProjection p outside left right q
          (p.slotEmbedding s) k)
        (CutNativeForms.spaceCast
          (CleanPhysicalReplay.cutSlots_fill p outside right).symm f) := by
  have h := inverse_spaceCast_HPullback
    (CleanPhysicalReplay.cutSlots_fill p outside left)
    (CleanPhysicalReplay.cutSlots_fill p outside right)
    (fun s k => CutProjectionAssembly.fillProjection p outside left right q
      (p.slotEmbedding s) k) f
  rw [projectionCast_fill] at h
  exact h

theorem scalarEquiv_fill_HPullback (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) (f : H right) :
    LowerCutNodeCoordinates.scalarEquiv p (CutSlotAssembly.fill p outside left)
        (CutNativeForms.spaceCast (CleanPhysicalReplay.cutSlots_fill p outside left).symm
          (HPullback q f)) =
      HPullback (ChildBlockProjection.nodeProjection
        (CutProjectionAssembly.fillProjection p outside left right q) (upperNode p))
        (LowerCutNodeCoordinates.scalarEquiv p (CutSlotAssembly.fill p outside right)
          (CutNativeForms.spaceCast
            (CleanPhysicalReplay.cutSlots_fill p outside right).symm f)) := by
  rw [fill_spaceCast_HPullback]
  exact scalarEquiv_HPullback p _ _ _ _

def nodeEquiv (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {a b : Nodes branch n} (hab : a = b) :
    H (nodeSlots slots a) ≃ₗ[F2] H (nodeSlots slots b) := by
  rw [hab]

theorem nodeEquiv_HPullback
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    {a b : Nodes branch n} (hab : a = b) (f : H (nodeSlots projected a)) :
    nodeEquiv slots hab (HPullback (ChildBlockProjection.nodeProjection q a) f) =
      HPullback (ChildBlockProjection.nodeProjection q b) (nodeEquiv projected hab f) := by
  cases hab
  rfl

theorem spaceEquiv_HPullback (p : Path branch n (m + 1))
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) (level : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper level)
    (hnode : upperNode p = HierarchicalLeftDecoder.LowerNode upper level d)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (f : H (subtreeSlots p projected)) :
    LowerCutDecoderForm.spaceEquiv p slots upper level d hnode
        (HPullback (fun s k => q (p.slotEmbedding s) k) f) =
      HPullback (ChildBlockProjection.nodeProjection q
        (HierarchicalLeftDecoder.LowerNode upper level d))
        (LowerCutDecoderForm.spaceEquiv p projected upper level d hnode f) := by
  change nodeEquiv slots hnode
      (LowerCutNodeCoordinates.scalarEquiv p slots
        (HPullback (fun s k => q (p.slotEmbedding s) k) f)) =
    HPullback (ChildBlockProjection.nodeProjection q
      (HierarchicalLeftDecoder.LowerNode upper level d))
      (nodeEquiv projected hnode (LowerCutNodeCoordinates.scalarEquiv p projected f))
  rw [scalarEquiv_HPullback, nodeEquiv_HPullback]

theorem spaceEquiv_fill_HPullback (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) (level : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper level)
    (hnode : upperNode p = HierarchicalLeftDecoder.LowerNode upper level d)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) (f : H right) :
    LowerCutDecoderForm.spaceEquiv p (CutSlotAssembly.fill p outside left)
        upper level d hnode
        (CutNativeForms.spaceCast (CleanPhysicalReplay.cutSlots_fill p outside left).symm
          (HPullback q f)) =
      HPullback (ChildBlockProjection.nodeProjection
        (CutProjectionAssembly.fillProjection p outside left right q)
        (HierarchicalLeftDecoder.LowerNode upper level d))
        (LowerCutDecoderForm.spaceEquiv p (CutSlotAssembly.fill p outside right)
          upper level d hnode
          (CutNativeForms.spaceCast
            (CleanPhysicalReplay.cutSlots_fill p outside right).symm f)) := by
  rw [fill_spaceCast_HPullback]
  exact spaceEquiv_HPullback p _ _ upper level d hnode _ _

end
end PerfectCompleteness.LowerCutScalarProjection

end

section

namespace PerfectCompleteness.SourceQuestionLowerForms

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

section Casts

variable {branch : Nat → Nat} {height t : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat)
  {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}

def rawCast (h : source = target) :
    CutChildGrouping.Raw (C := C) source rows ≃ CutChildGrouping.Raw (C := C) target rows := by
  cases h
  exact Equiv.refl _

theorem rawCast_law (h : source = target) :
    (CutChildGrouping.rawLaw (C := C) source rows).pushforward (rawCast rows h) =
      CutChildGrouping.rawLaw (C := C) target rows := by
  cases h
  exact FiniteDistribution.pushforward_id _

theorem formCast_injective (h : source = target) :
    Function.Injective (CutNativeForms.formCast h) := by
  cases h
  exact Function.injective_id

theorem fullCollision_formCast (h : source = target)
    (F G : Option (ChildBilinearCollisionTransfer.ParentForm source)) :
    BilinearCollisionTransfer.fullCollision (F.map (CutNativeForms.formCast h))
        (G.map (CutNativeForms.formCast h)) =
      BilinearCollisionTransfer.fullCollision F G :=
  MultiplicationFormInjective.definedEqual_map_of_injective
    (CutNativeForms.formCast h) (formCast_injective h) F G

end Casts

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)

abbrev Questions := SourceChildMarkedLaw.Questions
  (branch := branch) (n := height) (t := t) (m := m)
abbrev Calls := Option (WholeCutCalls.Index rows repeats path)

def slots (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill path outside (SourceChildMarkedLaw.questionSlots clauses q)

abbrev Raw (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :=
  CutChildGrouping.Raw (C := Calls (rows := rows) (repeats := repeats) path)
    (SourceChildMarkedLaw.questionSlots clauses q) rows

abbrev Form (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :=
  ChildBilinearCollisionTransfer.ParentForm (SourceChildMarkedLaw.questionSlots clauses q)

theorem cutSlots_eq (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    WholeCutGrouping.cutSlots path (slots path outside clauses q) =
      SourceChildMarkedLaw.questionSlots clauses q :=
  CleanPhysicalReplay.cutSlots_fill path outside _

def rawAtCut (q : Questions (branch := branch) (height := height) (t := t) (m := m))
    (raw : Raw (rows := rows) (repeats := repeats) path clauses q) :
    LowerCutPair.Raw rows repeats path (slots path outside clauses q) :=
  rawCast rows (cutSlots_eq path outside clauses q).symm raw

theorem rawAtCut_law
    (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    (CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
      (SourceChildMarkedLaw.questionSlots clauses q) rows).pushforward
        (rawAtCut (rows := rows) (repeats := repeats) path outside clauses q) =
      CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
        (WholeCutGrouping.cutSlots path (slots path outside clauses q)) rows :=
  rawCast_law rows (cutSlots_eq path outside clauses q).symm

variable (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)

abbrev UpperTable (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :=
  HierarchicalAllDecoderTables.Input (rows := rows)
    (slots path outside clauses q) upper level adviceRows →
      HierarchicalAllDecoderTables.UpperAnswer (slots path outside clauses q) upper

variable (tables : (q : Questions (branch := branch) (height := height) (t := t) (m := m)) →
  UpperTable (rows := rows) path outside clauses upper level (adviceRows := adviceRows) q)
  (cutoff : Nat)

def first (q : Questions (branch := branch) (height := height) (t := t) (m := m))
    (raw : Raw (rows := rows) (repeats := repeats) path clauses q) : Option (Form clauses q) :=
  (LowerCutDecoderForm.first path (slots path outside clauses q) upper level d hnode hbranch A
    (tables q) cutoff
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
      (SourceChildMarkedLaw.questionSlots clauses q) exterior)
    (rawAtCut path outside clauses q raw)).map
      (CutNativeForms.formCast (cutSlots_eq path outside clauses q))

def second (direction : BucketSampler.Direction (rows (height + 1)))
    (q : Questions (branch := branch) (height := height) (t := t) (m := m))
    (raw : Raw (rows := rows) (repeats := repeats) path clauses q) : Option (Form clauses q) :=
  (LowerCutDecoderForm.second path (slots path outside clauses q) upper level d hnode hbranch A
    (tables q) cutoff
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
      (SourceChildMarkedLaw.questionSlots clauses q) exterior)
    direction (rawAtCut path outside clauses q raw)).map
      (CutNativeForms.formCast (cutSlots_eq path outside clauses q))

theorem fullCollision_probability
    (direction : BucketSampler.Direction (rows (height + 1)))
    (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    (CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
      (SourceChildMarkedLaw.questionSlots clauses q) rows).probability
        (fun raw => BilinearCollisionTransfer.fullCollision
          (first path outside placeholder clauses upper level d hnode hbranch A exterior tables cutoff q raw)
          (second path outside placeholder clauses upper level d hnode hbranch A exterior tables cutoff
            direction q raw)) =
      (CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
        (WholeCutGrouping.cutSlots path (slots path outside clauses q)) rows).probability
        (fun raw => BilinearCollisionTransfer.fullCollision
          (LowerCutDecoderForm.first path (slots path outside clauses q) upper level d hnode hbranch A
            (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
              (SourceChildMarkedLaw.questionSlots clauses q) exterior) raw)
          (LowerCutDecoderForm.second path (slots path outside clauses q) upper level d hnode hbranch A
            (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
              (SourceChildMarkedLaw.questionSlots clauses q) exterior) direction raw)) := by
  have h := congrArg (fun μ : FiniteDistribution
      (CutChildGrouping.Raw (C := Calls (rows := rows) (repeats := repeats) path)
        (WholeCutGrouping.cutSlots path (slots path outside clauses q)) rows) => μ.probability
    (fun raw => BilinearCollisionTransfer.fullCollision
      (LowerCutDecoderForm.first path (slots path outside clauses q) upper level d hnode hbranch A
        (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
          (SourceChildMarkedLaw.questionSlots clauses q) exterior) raw)
      (LowerCutDecoderForm.second path (slots path outside clauses q) upper level d hnode hbranch A
        (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
          (SourceChildMarkedLaw.questionSlots clauses q) exterior) direction raw)))
    (rawAtCut_law (rows := rows) (repeats := repeats) path outside clauses q)
  rw [FiniteDistribution.probability_pushforward] at h
  simpa only [first, second, fullCollision_formCast] using h

end
end PerfectCompleteness.SourceQuestionLowerForms

end

end OAI
