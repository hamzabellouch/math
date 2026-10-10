import OAI.Computability.PerfectCompleteness.Construction.SourceChildKernelLemmas
import OAI.Computability.PerfectCompleteness.Foundations.CutSlotOutside
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutExteriorTransportLemmas
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayGroupingTransport
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanEndpointSlots
import OAI.Computability.PerfectCompleteness.Repetition.CleanRecordChildBlocks

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalReplay

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)

abbrev Exterior := WholeCutGrouping.Exterior rows repeats p
  (CutSlotAssembly.fill p outside placeholder)

def exteriorAt (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutGrouping.Exterior rows repeats p (CutSlotAssembly.fill p outside inside) :=
  WholeCutExteriorTransport.equiv rows repeats p
    (CutSlotAssembly.fill p outside placeholder) (CutSlotAssembly.fill p outside inside)
    (CutSlotAssembly.fill_outside_eq p outside placeholder inside) external

theorem cutSlots_fill (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot) :
    WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside) = inside := by
  funext s
  exact CutSlotAssembly.fill_at_cut p outside inside s

theorem childSlots_fill (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h)) :
    childSlots (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) i =
      childSlots inside i :=
  congrArg (fun ss => childSlots ss i) (cutSlots_fill p outside inside)

def fillChild (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h))
    (block : CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i) :
    CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows i :=
  cast (congrArg (SourceChildKernel.Block (WholeCutCalls.Index rows repeats p) rows)
    (childSlots_fill p outside inside i).symm) block

theorem fillChild_heq (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h))
    (block : CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i) :
    HEq (fillChild rows repeats p outside inside i block) block :=
  cast_heq _ _

private theorem cast_zeroBlock {n : Nat} {C : Type*} [Fintype C]
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target) :
    cast (congrArg (SourceChildKernel.Block C rows) hs)
        (SourceChildKernel.zeroBlock (C := C) rows slots) =
      SourceChildKernel.zeroBlock rows target := by
  cases hs
  rfl

theorem fillChild_zero (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h)) :
    fillChild rows repeats p outside inside i
        (SourceChildKernel.zeroBlock rows (childSlots inside i)) =
      SourceChildKernel.zeroBlock rows
        (childSlots (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) i) :=
  cast_zeroBlock rows _ _ (childSlots_fill p outside inside i).symm

def retainedAt (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (children : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i.val) :
    WholeCutReplayGrouping.RetainedChildren rows repeats p
      (CutSlotAssembly.fill p outside inside) clean :=
  fun i => fillChild rows repeats p outside inside i.val (children i)

def assembleAt (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (external : Exterior rows repeats p outside placeholder)
    (children : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i.val) :
    WholeCutReplay.Tape rows repeats p (CutSlotAssembly.fill p outside inside) clean :=
  WholeCutReplayGrouping.assemble rows repeats p (CutSlotAssembly.fill p outside inside) clean
    (exteriorAt rows repeats p outside placeholder inside external)
    (retainedAt rows repeats p outside inside clean children)

def physicalTape (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    WholeCutSampler.Tape rows repeats p (CutSlotAssembly.fill p outside inside) :=
  (WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm
    (exteriorAt rows repeats p outside placeholder inside external,
      fun i => fillChild rows repeats p outside inside i (children i))

theorem assembleAt_eq_erase (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    assembleAt rows repeats p outside placeholder inside clean external (fun i => children i.val) =
      WholeCutReplay.erase rows repeats p (CutSlotAssembly.fill p outside inside) clean
        (physicalTape rows repeats p outside placeholder inside external children) := by
  have h := WholeCutReplayGrouping.assemble_splitTape rows repeats p
    (CutSlotAssembly.fill p outside inside) clean
    (physicalTape rows repeats p outside placeholder inside external children)
  change WholeCutReplayGrouping.assemble rows repeats p (CutSlotAssembly.fill p outside inside) clean
      (exteriorAt rows repeats p outside placeholder inside external)
      (fun child => fillChild rows repeats p outside inside child.val (children child.val)) =
    WholeCutReplay.erase rows repeats p (CutSlotAssembly.fill p outside inside) clean
      (physicalTape rows repeats p outside placeholder inside external children)
  simpa only [physicalTape, Equiv.apply_symm_apply] using h

theorem physicalTape_grouped_zero
    (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows)
    (hzero : ∀ i, clean i → children i =
      SourceChildKernel.zeroBlock rows (childSlots inside i)) :
    WholeCutZero.GroupedAtClean rows repeats p (CutSlotAssembly.fill p outside inside) clean
      (physicalTape rows repeats p outside placeholder inside external children) := by
  intro i hi
  have hz : fillChild rows repeats p outside inside i (children i) =
      SourceChildKernel.zeroBlock rows
        (childSlots (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) i) := by
    rw [hzero i hi]
    exact fillChild_zero rows repeats p outside inside i
  change (∀ q, ((WholeCutGrouping.splitTape rows repeats p
      (CutSlotAssembly.fill p outside inside)
      (physicalTape rows repeats p outside placeholder inside external children)).2 i).1 q = 0) ∧ _
  simp only [physicalTape, Equiv.apply_symm_apply]
  rw [hz]
  exact ⟨fun _ => rfl, fun _ _ => rfl⟩

private theorem exteriorAt_heq
    (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p outside placeholder) :
    HEq (exteriorAt rows repeats p outside placeholder inside external) external :=
  cast_heq _ _

theorem transport_assembleAt
    (inside target : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (hs : ∀ i, ¬ clean i → ∀ s, inside (i, s) = target (i, s))
    (external : Exterior rows repeats p outside placeholder)
    (children : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i.val)
    (other : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) target rows i.val)
    (hc : ∀ i, HEq (children i) (other i)) :
    WholeCutReplayKeys.transportTape rows repeats p
        (CutSlotAssembly.fill p outside inside) (CutSlotAssembly.fill p outside target) clean
        (CutSlotAssembly.fill_kept_eq p outside inside target clean hs)
        (assembleAt rows repeats p outside placeholder inside clean external children) =
      assembleAt rows repeats p outside placeholder target clean external other := by
  unfold assembleAt
  rw [WholeCutReplayGroupingTransport.transport_assemble]
  apply congrArg₂ (WholeCutReplayGrouping.assemble rows repeats p
    (CutSlotAssembly.fill p outside target) clean)
  · apply eq_of_heq
    exact (cast_heq _ _).trans
      ((exteriorAt_heq rows repeats p outside placeholder inside external).trans
        (exteriorAt_heq rows repeats p outside placeholder target external).symm)
  · funext i
    apply eq_of_heq
    exact (WholeCutReplayGroupingTransport.castChildren_apply_heq rows repeats p
      (CutSlotAssembly.fill p outside inside) (CutSlotAssembly.fill p outside target) clean
      (CutSlotAssembly.fill_kept_eq p outside inside target clean hs)
      (retainedAt rows repeats p outside inside clean children) i).trans
        ((fillChild_heq rows repeats p outside inside i.val (children i)).trans
          ((hc i).trans (fillChild_heq rows repeats p outside target i.val (other i)).symm))

section Source

variable {v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Record := CleanRecordChildBlocks.Record
  (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated

abbrev Sample := SourceChildKernel.Sample
  (C := WholeCutCalls.Index rows repeats p) (t := t) rows clauses designated

def leftRecord (record : Record (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.leftRef rows clauses designated record))
      (CleanRecordChildBlocks.clean rows clauses designated record) :=
  assembleAt rows repeats p outside placeholder
    (CleanRecordChildBlocks.leftRef rows clauses designated record)
    (CleanRecordChildBlocks.clean rows clauses designated record) external
    (CleanRecordChildBlocks.leftChild rows clauses designated record)

def rightRecord (record : Record (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.rightRef rows clauses designated record))
      (CleanRecordChildBlocks.clean rows clauses designated record) :=
  assembleAt rows repeats p outside placeholder
    (CleanRecordChildBlocks.rightRef rows clauses designated record)
    (CleanRecordChildBlocks.clean rows clauses designated record) external
    (CleanRecordChildBlocks.rightChild rows clauses designated record)

def leftInside (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  SourceChildKernel.parentLeftSlots clauses designated (fun i => ((x i).1, (x i).2.1))

def rightInside (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  SourceChildKernel.parentRightSlots rows clauses designated
    (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)

def leftBlocks (x : Sample (t := t) rows repeats p clauses designated) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (leftInside rows repeats p clauses designated x) rows :=
  SourceChildKernel.leftChildren rows clauses designated
    (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)

def rightBlocks (x : Sample (t := t) rows repeats p clauses designated) :
    CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (rightInside rows repeats p clauses designated x) rows :=
  SourceChildKernel.rightChildren rows clauses designated
    (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)

def leftTape (x : Sample (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutSampler.Tape rows repeats p
      (CutSlotAssembly.fill p outside (leftInside rows repeats p clauses designated x)) :=
  physicalTape rows repeats p outside placeholder (leftInside rows repeats p clauses designated x)
    external (leftBlocks rows repeats p clauses designated x)

def rightTape (x : Sample (t := t) rows repeats p clauses designated)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutSampler.Tape rows repeats p
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x)) :=
  physicalTape rows repeats p outside placeholder (rightInside rows repeats p clauses designated x)
    external (rightBlocks rows repeats p clauses designated x)

theorem leftInside_nonclean (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (i : Fin (branch h)) (hi : ¬ CleanRecordChildBlocks.clean rows clauses designated record i)
    (s : Slots branch h) :
    CleanRecordChildBlocks.leftRef rows clauses designated record (i, s) =
      leftInside rows repeats p clauses designated x (i, s) :=
  congrFun (CleanRecordChildBlocks.leftRef_childSlots_event
    rows clauses designated record x hevent ⟨i, hi⟩) s

theorem rightInside_nonclean (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (i : Fin (branch h)) (hi : ¬ CleanRecordChildBlocks.clean rows clauses designated record i)
    (s : Slots branch h) :
    CleanRecordChildBlocks.rightRef rows clauses designated record (i, s) =
      rightInside rows repeats p clauses designated x (i, s) :=
  congrFun (CleanRecordChildBlocks.rightRef_childSlots_event
    rows clauses designated record x hevent ⟨i, hi⟩) s

theorem leftRecord_eq_erase (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutReplayKeys.transportTape rows repeats p
      (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.leftRef rows clauses designated record))
      (CutSlotAssembly.fill p outside (leftInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (CutSlotAssembly.fill_kept_eq p outside _ _ _
        (leftInside_nonclean rows repeats p clauses designated record x hevent))
      (leftRecord rows repeats p outside placeholder clauses designated record external) =
    WholeCutReplay.erase rows repeats p
      (CutSlotAssembly.fill p outside (leftInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (leftTape rows repeats p outside placeholder clauses designated x external) := by
  exact (transport_assembleAt rows repeats p outside placeholder _ _ _
    (leftInside_nonclean rows repeats p clauses designated record x hevent) external _ _
    (CleanRecordChildBlocks.leftChild_event_heq rows clauses designated record x hevent)).trans
      (assembleAt_eq_erase rows repeats p outside placeholder _ _ external
        (leftBlocks rows repeats p clauses designated x))

theorem rightRecord_eq_erase (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutReplayKeys.transportTape rows repeats p
      (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.rightRef rows clauses designated record))
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (CutSlotAssembly.fill_kept_eq p outside _ _ _
        (rightInside_nonclean rows repeats p clauses designated record x hevent))
      (rightRecord rows repeats p outside placeholder clauses designated record external) =
    WholeCutReplay.erase rows repeats p
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (rightTape rows repeats p outside placeholder clauses designated x external) := by
  exact (transport_assembleAt rows repeats p outside placeholder _ _ _
    (rightInside_nonclean rows repeats p clauses designated record x hevent) external _ _
    (CleanRecordChildBlocks.rightChild_event_heq rows clauses designated record x hevent)).trans
      (assembleAt_eq_erase rows repeats p outside placeholder _ _ external
        (rightBlocks rows repeats p clauses designated x))

variable
  (μ : Fin (branch h) → FiniteDistribution (SourceQuestionReconstruction.SourceTuple m t))
  (ν : (i : Fin (branch h)) → FiniteDistribution
    (SourceChildKernel.Rest (m := m) (t := t) designated i))
  (flag : Fin (branch h) → FiniteDistribution Bool)

omit [NeZero m] in
theorem rightBlocks_zero (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (i : Fin (branch h)) (hi : CleanRecordChildBlocks.clean rows clauses designated record i) :
    rightBlocks rows repeats p clauses designated x i =
      SourceChildKernel.zeroBlock rows
        (childSlots (rightInside rows repeats p clauses designated x) i) :=
  SourceChildKernel.childrenLaw_clean_zero rows clauses designated μ ν flag x hx i
    (CleanRecordChildBlocks.childClean_of_clean rows clauses designated record x hevent i hi)

omit [NeZero m] in
theorem leftBlocks_zero (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (i : Fin (branch h)) (hi : CleanRecordChildBlocks.clean rows clauses designated record i) :
    leftBlocks rows repeats p clauses designated x i =
      SourceChildKernel.zeroBlock rows
        (childSlots (leftInside rows repeats p clauses designated x) i) := by
  have hz := rightBlocks_zero rows repeats p clauses designated μ ν flag record x hx hevent i hi
  change ChildAssemblyProjection.childPullback rows
    (SourceChildKernel.parentProjection rows clauses designated
      (fun j => ((x j).1, (x j).2.1)) (fun j => (x j).2.2)) i
    (rightBlocks rows repeats p clauses designated x i) = _
  rw [hz]
  exact map_zero _

omit [NeZero m] in
theorem rightTape_grouped_zero (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutZero.GroupedAtClean rows repeats p
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (rightTape rows repeats p outside placeholder clauses designated x external) :=
  physicalTape_grouped_zero rows repeats p outside placeholder _ _ external _
    (rightBlocks_zero rows repeats p clauses designated μ ν flag record x hx hevent)

omit [NeZero m] in
theorem leftTape_grouped_zero (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutZero.GroupedAtClean rows repeats p
      (CutSlotAssembly.fill p outside (leftInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (leftTape rows repeats p outside placeholder clauses designated x external) :=
  physicalTape_grouped_zero rows repeats p outside placeholder _ _ external _
    (leftBlocks_zero rows repeats p clauses designated μ ν flag record x hx hevent)

private theorem response_of_erase {Y : Type*}
    (slots target : Slots branch root → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (hs : ∀ s, CutSamplerKeyLocality.keptLeaf p clean s → slots s = target s)
    (reference : WholeCutReplay.Tape rows repeats p slots clean)
    (tape : WholeCutSampler.Tape rows repeats p target)
    (htape : WholeCutReplayKeys.transportTape rows repeats p slots target clean hs reference =
      WholeCutReplay.erase rows repeats p target clean tape)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p target clean tape)
    (post : Output branch root rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch root t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
      (WholeCutReplayKeys.query rows repeats p slots clean reference post) =
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots target)
      (WholeCutKeyLocality.query rows repeats p target tape post) := by
  have h := WholeCutReplayKeys.response_eq_transport rows repeats p slots target clean hs
    reference post labeling side
  rw [htape, WholeCutReplayKeys.query_erase rows repeats p target clean tape post hzero] at h
  exact h

theorem leftRecord_response_eq {Y : Type*}
    (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder)
    (post : Output branch root rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch root t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side
      (TreeCanonical.numberedSlots
        (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.leftRef rows clauses designated record)))
      (WholeCutReplayKeys.query rows repeats p
        (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.leftRef rows clauses designated record))
        (CleanRecordChildBlocks.clean rows clauses designated record)
        (leftRecord rows repeats p outside placeholder clauses designated record external) post) =
    KeyStrategy.response labeling side
      (TreeCanonical.numberedSlots
        (CutSlotAssembly.fill p outside (leftInside rows repeats p clauses designated x)))
      (WholeCutKeyLocality.query rows repeats p
        (CutSlotAssembly.fill p outside (leftInside rows repeats p clauses designated x))
        (leftTape rows repeats p outside placeholder clauses designated x external) post) :=
  response_of_erase rows repeats p _ _ _
    (CutSlotAssembly.fill_kept_eq p outside _ _ _
      (leftInside_nonclean rows repeats p clauses designated record x hevent)) _ _
    (leftRecord_eq_erase rows repeats p outside placeholder clauses designated record x hevent external)
    (leftTape_grouped_zero rows repeats p outside placeholder clauses designated μ ν flag
      record x hx hevent external) post labeling side

theorem rightRecord_response_eq {Y : Type*}
    (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder)
    (post : Output branch root rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch root t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side
      (TreeCanonical.numberedSlots
        (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.rightRef rows clauses designated record)))
      (WholeCutReplayKeys.query rows repeats p
        (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.rightRef rows clauses designated record))
        (CleanRecordChildBlocks.clean rows clauses designated record)
        (rightRecord rows repeats p outside placeholder clauses designated record external) post) =
    KeyStrategy.response labeling side
      (TreeCanonical.numberedSlots
        (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x)))
      (WholeCutKeyLocality.query rows repeats p
        (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x))
        (rightTape rows repeats p outside placeholder clauses designated x external) post) :=
  response_of_erase rows repeats p _ _ _
    (CutSlotAssembly.fill_kept_eq p outside _ _ _
      (rightInside_nonclean rows repeats p clauses designated record x hevent)) _ _
    (rightRecord_eq_erase rows repeats p outside placeholder clauses designated record x hevent external)
    (rightTape_grouped_zero rows repeats p outside placeholder clauses designated μ ν flag
      record x hx hevent external) post labeling side

end Source

section OwnReplay

variable {v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  (record : Record (t := t) rows repeats p clauses designated)
  (external : Exterior rows repeats p outside placeholder)

def leftReplay
    (own : {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      Fin t → Fin m) :=
  CleanEndpointSlots.leftReplay clauses designated
    (CleanRecordChildBlocks.clean rows clauses designated record)
    (CleanRecordChildBlocks.visible rows clauses designated record) rows repeats p outside
    (leftRecord rows repeats p outside placeholder clauses designated record external) own

def rightReplay
    (own : {i : Fin (branch h) // CleanRecordChildBlocks.clean rows clauses designated record i} →
      Fin t → Fin v) :=
  CleanEndpointSlots.rightReplay clauses designated
    (CleanRecordChildBlocks.clean rows clauses designated record)
    (CleanRecordChildBlocks.visible rows clauses designated record) rows repeats p outside
    (CleanRecordChildBlocks.projected rows clauses designated record)
    (rightRecord rows repeats p outside placeholder clauses designated record external) own

end OwnReplay

end
end PerfectCompleteness.CleanPhysicalReplay

end

end OAI
