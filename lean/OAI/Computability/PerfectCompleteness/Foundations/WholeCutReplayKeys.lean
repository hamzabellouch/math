import OAI.Computability.PerfectCompleteness.Construction.WholeCutLocalityLemmas
import OAI.Computability.PerfectCompleteness.Foundations.RetainedKeyTransport
import OAI.Computability.PerfectCompleteness.Foundations.WholeCutReplayLemmas

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplayKeys

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat} {Y : Type*}

def leafEquiv (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (s : Slots branch n) (hkeep : keptLeaf p clean s) :
    LeafDomain slots s ≃ LeafDomain target s :=
  Equiv.cast (congrArg MixedSupport.Assignment (hs s hkeep))

def transportTape (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutReplay.Tape rows repeats p slots clean) :
    WholeCutReplay.Tape rows repeats p target clean :=
  WholeCutReplayTransport.transport rows repeats p slots target clean
    (leafEquiv p slots target clean hs) tape

def query (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutReplay.Tape rows repeats p slots clean)
    (post : Output branch n rows → Y) :
    MixedSupport.Assignment (TreeCanonical.numberedSlots slots) → Y :=
  post ∘ TreeCanonical.numberedFunction slots (WholeCutReplay.fullQuery rows repeats p slots clean tape)

theorem numberedSlotEquality (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (j : Fin (TreeCanonical.locationCount branch n t)) (hj : numberedKeep p clean j) :
    TreeCanonical.numberedSlots slots j = TreeCanonical.numberedSlots target j :=
  congrFun (hs ((TreeCanonical.numbering branch n t).symm j).1 hj)
    ((TreeCanonical.numbering branch n t).symm j).2

private theorem assignmentEquiv_symm_apply
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (x : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (s : Slots branch n) (k : Fin t) :
    HEq ((TreeCanonical.assignmentEquiv slots).symm x s k)
      (x (TreeCanonical.numbering branch n t (s, k))) := by
  have h := congrFun ((TreeCanonical.assignmentEquiv slots).apply_symm_apply x)
    (TreeCanonical.numbering branch n t (s, k))
  exact Eq.mp (congrArg (fun sk : TreeCanonical.Location branch n t =>
    HEq ((TreeCanonical.assignmentEquiv slots).symm x sk.1 sk.2)
      (x (TreeCanonical.numbering branch n t (s, k))))
    ((TreeCanonical.numbering branch n t).symm_apply_apply (s, k))) (heq_of_eq h)

private theorem assignmentCast_eq {I : Type*} {slots target : I → MixedSupport.Slot}
    (h : slots = target) (x : MixedSupport.Assignment slots)
    (y : MixedSupport.Assignment target) (hxy : ∀ i, HEq (x i) (y i)) :
    Equiv.cast (congrArg MixedSupport.Assignment h) x = y := by
  cases h
  funext i
  exact eq_of_heq (hxy i)

theorem leaf_agreement (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (x : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (y : MixedSupport.Assignment (TreeCanonical.numberedSlots target))
    (hret : RetainedKeyTransport.retainedAssignmentEquiv
        (TreeCanonical.numberedSlots slots) (TreeCanonical.numberedSlots target)
        (numberedKeep p clean) (numberedSlotEquality p slots target clean hs)
        (CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) x) =
      CleanKeyErasure.retain (TreeCanonical.numberedSlots target) (numberedKeep p clean) y) :
    ∀ s hkeep, leafEquiv p slots target clean hs s hkeep
        ((TreeCanonical.assignmentEquiv slots).symm x s) =
      (TreeCanonical.assignmentEquiv target).symm y s := by
  intro s hkeep
  change Equiv.cast (congrArg MixedSupport.Assignment (hs s hkeep))
      ((TreeCanonical.assignmentEquiv slots).symm x s) =
    (TreeCanonical.assignmentEquiv target).symm y s
  apply assignmentCast_eq (hs s hkeep)
  intro k
  have hj : numberedKeep p clean (TreeCanonical.numbering branch n t (s, k)) := by
    simpa only [numberedKeep, Equiv.symm_apply_apply] using hkeep
  have hnumbered := RetainedKeyTransport.retainedAssignmentEquiv_agree_heq
    (TreeCanonical.numberedSlots slots) (TreeCanonical.numberedSlots target)
    (numberedKeep p clean) (numberedSlotEquality p slots target clean hs) x y hret
    (TreeCanonical.numbering branch n t (s, k)) hj
  exact (assignmentEquiv_symm_apply slots x s k).trans
    (hnumbered.trans (assignmentEquiv_symm_apply target y s k).symm)

theorem query_agreement (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutReplay.Tape rows repeats p slots clean) (post : Output branch n rows → Y)
    (x : MixedSupport.Assignment (TreeCanonical.numberedSlots slots))
    (y : MixedSupport.Assignment (TreeCanonical.numberedSlots target))
    (hret : RetainedKeyTransport.retainedAssignmentEquiv
        (TreeCanonical.numberedSlots slots) (TreeCanonical.numberedSlots target)
        (numberedKeep p clean) (numberedSlotEquality p slots target clean hs)
        (CleanKeyErasure.retain (TreeCanonical.numberedSlots slots) (numberedKeep p clean) x) =
      CleanKeyErasure.retain (TreeCanonical.numberedSlots target) (numberedKeep p clean) y) :
    query rows repeats p slots clean tape post x =
      query rows repeats p target clean (transportTape rows repeats p slots target clean hs tape)
        post y :=
  congrArg post (WholeCutReplayTransport.fullQuery_transport rows repeats p slots target clean
    (leafEquiv p slots target clean hs) tape
    ((TreeCanonical.assignmentEquiv slots).symm x)
    ((TreeCanonical.assignmentEquiv target).symm y)
    (leaf_agreement p slots target clean hs x y hret)).symm

theorem key_eq_transport (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutReplay.Tape rows repeats p slots clean) (post : Output branch n rows → Y)
    (side : CanonicalKeys.Side) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots)
        (query rows repeats p slots clean tape post) =
      CanonicalKeys.key side (TreeCanonical.numberedSlots target)
        (query rows repeats p target clean (transportTape rows repeats p slots target clean hs tape) post) :=
  RetainedKeyTransport.key_eq side (TreeCanonical.numberedSlots slots)
    (TreeCanonical.numberedSlots target) (numberedKeep p clean)
    (numberedSlotEquality p slots target clean hs) _ _
    (query_agreement rows repeats p slots target clean hs tape post)

theorem label_val_eq_transport (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutReplay.Tape rows repeats p slots clean) (post : Output branch n rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    (KeyStrategy.label labeling side (TreeCanonical.numberedSlots slots)
        (query rows repeats p slots clean tape post)).val =
      (KeyStrategy.label labeling side (TreeCanonical.numberedSlots target)
        (query rows repeats p target clean
          (transportTape rows repeats p slots target clean hs tape) post)).val :=
  KeyStrategy.label_val_eq_of_key_eq labeling side side _ _ _ _
    (key_eq_transport rows repeats p slots target clean hs tape post side)

theorem response_eq_transport (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutReplay.Tape rows repeats p slots clean) (post : Output branch n rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
        (query rows repeats p slots clean tape post) =
      KeyStrategy.response labeling side (TreeCanonical.numberedSlots target)
        (query rows repeats p target clean
          (transportTape rows repeats p slots target clean hs tape) post) :=
  RetainedKeyTransport.response_eq labeling side (TreeCanonical.numberedSlots slots)
    (TreeCanonical.numberedSlots target) (numberedKeep p clean)
    (numberedSlotEquality p slots target clean hs) _ _
    (query_agreement rows repeats p slots target clean hs tape post)

theorem query_erase (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (post : Output branch n rows → Y)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) :
    query rows repeats p slots clean (WholeCutReplay.erase rows repeats p slots clean tape) post =
      WholeCutKeyLocality.query rows repeats p slots tape post := by
  funext x
  exact congrArg post (WholeCutReplay.fullQuery_erase_of_grouped_zero
    rows repeats p slots clean tape hzero ((TreeCanonical.assignmentEquiv slots).symm x))

theorem original_key_eq_transport (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutSampler.Tape rows repeats p slots) (post : Output branch n rows → Y)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (side : CanonicalKeys.Side) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots slots)
        (WholeCutKeyLocality.query rows repeats p slots tape post) =
      CanonicalKeys.key side (TreeCanonical.numberedSlots target)
        (query rows repeats p target clean (transportTape rows repeats p slots target clean hs
          (WholeCutReplay.erase rows repeats p slots clean tape)) post) := by
  rw [← query_erase rows repeats p slots clean tape post hzero]
  exact key_eq_transport rows repeats p slots target clean hs
    (WholeCutReplay.erase rows repeats p slots clean tape) post side

theorem original_response_eq_transport (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (tape : WholeCutSampler.Tape rows repeats p slots) (post : Output branch n rows → Y)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
        (WholeCutKeyLocality.query rows repeats p slots tape post) =
      KeyStrategy.response labeling side (TreeCanonical.numberedSlots target)
        (query rows repeats p target clean (transportTape rows repeats p slots target clean hs
          (WholeCutReplay.erase rows repeats p slots clean tape)) post) := by
  rw [← query_erase rows repeats p slots clean tape post hzero]
  exact response_eq_transport rows repeats p slots target clean hs
    (WholeCutReplay.erase rows repeats p slots clean tape) post labeling side

end
end PerfectCompleteness.WholeCutReplayKeys

end

end OAI
