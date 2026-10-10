import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanEndpointSlots

namespace OAI

section

namespace PerfectCompleteness.CleanRecordChildBlocks

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open SourceQuestionReconstruction

variable {branch : Nat → Nat} {h t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record :=
  CleanSourceRecord.Record
    (D := SourceChildKernel.D (C := C) (t := t) rows clauses designated) designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)

abbrev Sample := SourceChildKernel.Sample (C := C) (t := t) rows clauses designated

abbrev Row (i : Fin (branch h)) := SourceTuple m t ×
  (SourceChildKernel.Rest (m := m) (t := t) designated i ×
    SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

def clean (record : Record (C := C) (t := t) rows clauses designated) :
    Fin (branch h) → Prop :=
  CleanSourceRecord.clean designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record

def visible (record : Record (C := C) (t := t) rows clauses designated) :
    Visible (E := SourceTuple m t) designated (clean rows clauses designated record) :=
  CleanSourceRecord.visible designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record

def projected (record : Record (C := C) (t := t) rows clauses designated) :
    Fin (branch h) → Bool :=
  CleanSourceRecord.projected designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated) record

def event (record : Record (C := C) (t := t) rows clauses designated) :
    Sample (C := C) (t := t) rows clauses designated → Bool :=
  UniformCleanSources.recordEvent
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record

abbrev Nonclean (record : Record (C := C) (t := t) rows clauses designated) :=
  {i : Fin (branch h) // ¬ clean rows clauses designated record i}

def extract (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) : Row (C := C) (t := t) rows clauses designated i.val :=
  match hr : record i.val with
  | .inl row => row
  | .inr _ => False.elim (i.property (by
      simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord]))

theorem record_extract (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    record i.val = .inl (extract rows clauses designated record i) := by
  unfold extract
  split
  · rename_i row hr
    exact hr
  · rename_i rest hr
    exact False.elim (i.property (by
      simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord]))

theorem extract_eq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    extract rows clauses designated record i = x i.val := by
  have obs := CleanSourceRecord.observation_eq designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record x hevent i.val
  cases hc : UniformCleanSources.childClean
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
      i.val (x i.val).1 (x i.val).2.1 (x i.val).2.2 with
  | false =>
      have hr : record i.val = .inl (x i.val) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false]
          using obs.symm
      exact Sum.inl.inj ((record_extract rows clauses designated record i).symm.trans hr)
  | true =>
      have hr : record i.val = .inr (x i.val).2.1 := by
        simpa only [SelectedSources.childObservation, hc, ite_true] using obs.symm
      exact False.elim (i.property (by
        simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord]))

def source (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Source (m := m) (t := t) designated i.val :=
  ((extract rows clauses designated record i).1, (extract rows clauses designated record i).2.1)

def raw (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i.val :=
  (extract rows clauses designated record i).2.2

theorem visible_nonclean (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) (leaf : Slots branch h)
    (hleaf : ¬ (clean rows clauses designated record i.val ∧ leaf = designated i.val)) :
    visible rows clauses designated record i.val ⟨leaf, hleaf⟩ =
      SourceChildKernel.tree designated i.val (source rows clauses designated record i) leaf := by
  dsimp only [visible, CleanSourceRecord.visible]
  split
  · rename_i row hr
    have hrow : row = extract rows clauses designated record i :=
      Sum.inl.inj (hr.symm.trans (record_extract rows clauses designated record i))
    rw [hrow]
    rfl
  · rename_i rest hr
    have hbad := hr.symm.trans (record_extract rows clauses designated record i)
    cases hbad

theorem projected_nonclean (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    projected rows clauses designated record i.val =
      SourceChildKernel.rawProjected rows clauses designated i.val
        (raw rows clauses designated record i) := by
  simp only [projected, CleanSourceRecord.projected,
    record_extract rows clauses designated record i, raw,
    CleanSourceRecord.rawProjected, SourceChildKernel.rawProjected]
  cases (extract rows clauses designated record i).2.2 <;> rfl

variable [NeZero m]

def leftRef (record : Record (C := C) (t := t) rows clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.leftReference clauses designated (clean rows clauses designated record)
    (visible rows clauses designated record)

def rightRef (record : Record (C := C) (t := t) rows clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  CleanEndpointSlots.rightReference clauses designated (clean rows clauses designated record)
    (visible rows clauses designated record) (projected rows clauses designated record)

theorem leftRef_childSlots (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    childSlots (leftRef rows clauses designated record) i.val =
      SourceChildKernel.nativeSlots clauses designated i.val (source rows clauses designated record i) := by
  funext leaf k
  have hn : ¬ (clean rows clauses designated record i.val ∧ leaf = designated i.val) :=
    fun h => i.property h.1
  simp only [leftRef, CleanEndpointSlots.leftReference, CleanEndpointSlots.leftInside,
    childSlots, reconstructLeft, reconstruct, dite_eq_right hn]
  rw [visible_nonclean rows clauses designated record i leaf hn]
  rfl

theorem rightRef_childSlots (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    childSlots (rightRef rows clauses designated record) i.val =
      SourceChildKernel.mixedSlots clauses designated i.val (source rows clauses designated record i)
        (SourceChildKernel.rawProjected rows clauses designated i.val (raw rows clauses designated record i)) := by
  funext leaf k
  have hn : ¬ (clean rows clauses designated record i.val ∧ leaf = designated i.val) :=
    fun h => i.property h.1
  simp only [rightRef, CleanEndpointSlots.rightReference, CleanEndpointSlots.rightInside,
    childSlots, reconstructRight, reconstruct, dite_eq_right hn]
  rw [visible_nonclean rows clauses designated record i leaf hn,
    projected_nonclean rows clauses designated record i]
  exact (SourceChildKernel.mixedSlots_eq_rightTuple clauses designated i.val
    (source rows clauses designated record i)
    (SourceChildKernel.rawProjected rows clauses designated i.val (raw rows clauses designated record i))
    leaf k).symm

theorem leftRef_childSlots_event (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    childSlots (leftRef rows clauses designated record) i.val =
      childSlots (SourceChildKernel.parentLeftSlots clauses designated
        (fun j => ((x j).1, (x j).2.1))) i.val :=
  (leftRef_childSlots rows clauses designated record i).trans
    (congrArg (fun y : Row (C := C) (t := t) rows clauses designated i.val =>
      SourceChildKernel.nativeSlots clauses designated i.val (y.1, y.2.1))
      (extract_eq rows clauses designated record x hevent i))

theorem rightRef_childSlots_event (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    childSlots (rightRef rows clauses designated record) i.val =
      childSlots (SourceChildKernel.parentRightSlots rows clauses designated
        (fun j => ((x j).1, (x j).2.1)) (fun j => (x j).2.2)) i.val :=
  (rightRef_childSlots rows clauses designated record i).trans
    (congrArg (fun y : Row (C := C) (t := t) rows clauses designated i.val =>
      SourceChildKernel.mixedSlots clauses designated i.val (y.1, y.2.1)
        (SourceChildKernel.rawProjected rows clauses designated i.val y.2.2))
      (extract_eq rows clauses designated record x hevent i))

def physicalRight (i : Fin (branch h)) (row : Row (C := C) (t := t) rows clauses designated i) :
    SourceChildKernel.Block C rows (SourceChildKernel.mixedSlots clauses designated i (row.1, row.2.1)
      (SourceChildKernel.rawProjected rows clauses designated i row.2.2)) :=
  SourceChildKernel.decodeRight rows clauses designated i (row.1, row.2.1) row.2.2

def physicalLeft (i : Fin (branch h)) (row : Row (C := C) (t := t) rows clauses designated i) :
    SourceChildKernel.Block C rows (SourceChildKernel.nativeSlots clauses designated i (row.1, row.2.1)) :=
  let p := SourceChildKernel.projection clauses designated i (row.1, row.2.1)
    (SourceChildKernel.rawProjected rows clauses designated i row.2.2)
  let block := physicalRight rows clauses designated i row
  (fun call => ChildBlockProjection.squarePullback p (block.1 call),
    ChildBlockProjection.arraysPullback rows p block.2)

omit [NeZero m] in
theorem physicalLeft_eq_leftChildren
    (x : Sample (C := C) (t := t) rows clauses designated) (i : Fin (branch h)) :
    physicalLeft rows clauses designated i (x i) =
      SourceChildKernel.leftChildren rows clauses designated
        (fun j => ((x j).1, (x j).2.1)) (fun j => (x j).2.2) i := by
  rw [SourceChildKernel.leftChildren_apply]
  rfl

def rightChild (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Block C rows (childSlots (rightRef rows clauses designated record) i.val) :=
  cast (congrArg (SourceChildKernel.Block C rows) (rightRef_childSlots rows clauses designated record i).symm)
    (physicalRight rows clauses designated i.val (extract rows clauses designated record i))

def leftChild (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    SourceChildKernel.Block C rows (childSlots (leftRef rows clauses designated record) i.val) :=
  cast (congrArg (SourceChildKernel.Block C rows) (leftRef_childSlots rows clauses designated record i).symm)
    (physicalLeft rows clauses designated i.val (extract rows clauses designated record i))

theorem rightChild_heq (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    HEq (rightChild rows clauses designated record i)
      (physicalRight rows clauses designated i.val (extract rows clauses designated record i)) :=
  cast_heq _ _

theorem leftChild_heq (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    HEq (leftChild rows clauses designated record i)
      (physicalLeft rows clauses designated i.val (extract rows clauses designated record i)) :=
  cast_heq _ _

private theorem dependent_congr {A : Sort*} {B : A → Sort*} (f : (a : A) → B a)
    {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

theorem rightChild_event_heq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    HEq (rightChild rows clauses designated record i)
      (SourceChildKernel.rightChildren rows clauses designated
        (fun j => ((x j).1, (x j).2.1)) (fun j => (x j).2.2) i.val) :=
  (rightChild_heq rows clauses designated record i).trans
    (dependent_congr (physicalRight rows clauses designated i.val)
      (extract_eq rows clauses designated record x hevent i))

theorem leftChild_event_heq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    HEq (leftChild rows clauses designated record i)
      (SourceChildKernel.leftChildren rows clauses designated
        (fun j => ((x j).1, (x j).2.1)) (fun j => (x j).2.2) i.val) := by
  have hphysical :
      HEq (physicalLeft rows clauses designated i.val (extract rows clauses designated record i))
        (physicalLeft rows clauses designated i.val (x i.val)) :=
    dependent_congr (physicalLeft rows clauses designated i.val)
      (extract_eq rows clauses designated record x hevent i)
  exact (leftChild_heq rows clauses designated record i).trans
    (hphysical.trans (heq_of_eq (physicalLeft_eq_leftChildren rows clauses designated x i.val)))

omit [NeZero m] in
theorem childClean_of_clean (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true) (i : Fin (branch h))
    (hi : clean rows clauses designated record i) :
    UniformCleanSources.childClean
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
      i (x i).1 (x i).2.1 (x i).2.2 = true := by
  have obs := CleanSourceRecord.observation_eq designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record x hevent i
  cases hc : UniformCleanSources.childClean
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
      i (x i).1 (x i).2.1 (x i).2.2 with
  | false =>
      have hr : record i = .inl (x i) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false]
          using obs.symm
      simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord,
        Bool.false_eq_true] at hi
  | true => rfl

end
end PerfectCompleteness.CleanRecordChildBlocks

end

end OAI
