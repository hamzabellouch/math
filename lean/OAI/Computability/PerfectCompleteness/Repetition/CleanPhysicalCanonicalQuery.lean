import OAI.Computability.PerfectCompleteness.Decoding.WholeCutGroupedProjection
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalProjectedSliceLemmas

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalCanonicalQuery

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

abbrev Sample := CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated

def leftSlots (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (CleanPhysicalReplay.leftInside rows repeats p clauses designated x)

def rightSlots (x : Sample (t := t) rows repeats p clauses designated) :
    Slots branch root → Fin t → MixedSupport.Slot :=
  CutSlotAssembly.fill p outside (CleanPhysicalReplay.rightInside rows repeats p clauses designated x)

def projection (x : Sample (t := t) rows repeats p clauses designated) :
    ∀ s k, MixedSupport.Projection
      (leftSlots rows repeats p outside clauses designated x s k)
      (rightSlots rows repeats p outside clauses designated x s k) :=
  CutProjectionAssembly.fillProjection p outside _ _
    (SourceChildKernel.parentProjection rows clauses designated
      (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2))

def leftArrays (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    Arrays (leftSlots rows repeats p outside clauses designated x) rows :=
  WholeCutSampler.evaluate rows repeats p _
    (CleanPhysicalReplay.leftTape rows repeats p outside placeholder clauses designated x external)

def rightArrays (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    Arrays (rightSlots rows repeats p outside clauses designated x) rows :=
  WholeCutSampler.evaluate rows repeats p _
    (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated x external)

omit [NeZero m] in
theorem arrays_pullback (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    leftArrays rows repeats p outside placeholder clauses designated x external =
      ChildBlockProjection.arraysPullback rows
        (projection rows repeats p outside clauses designated x)
        (rightArrays rows repeats p outside placeholder clauses designated x external) :=
  WholeCutGroupedProjection.physicalTape_pullback rows repeats p outside placeholder
    (CleanPhysicalReplay.leftInside rows repeats p clauses designated x)
    (CleanPhysicalReplay.rightInside rows repeats p clauses designated x)
    (SourceChildKernel.parentProjection rows clauses designated
      (fun i => ((x i).1, (x i).2.1)) (fun i => (x i).2.2)) external
    (CleanPhysicalReplay.rightBlocks rows repeats p clauses designated x)

omit [NeZero m] in
theorem query_pullback {Y : Type*}
    (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (post : Output branch root rows → Y) :
    WholeCutKeyLocality.query rows repeats p
        (leftSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.leftTape rows repeats p outside placeholder clauses designated x external) post =
      WholeCutKeyLocality.query rows repeats p
        (rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated x external) post ∘
          MixedSupport.projectionMap (TreeCanonical.numberedProjection
            (projection rows repeats p outside clauses designated x)) := by
  change SourceProjectedCanonicalQuery.query rows
      (leftArrays rows repeats p outside placeholder clauses designated x external) post =
    SourceProjectedCanonicalQuery.query rows
      (rightArrays rows repeats p outside placeholder clauses designated x external) post ∘ _
  rw [arrays_pullback]
  exact SourceProjectedCanonicalQuery.query_pullback rows
    (projection rows repeats p outside clauses designated x)
    (rightArrays rows repeats p outside placeholder clauses designated x external) post

omit [NeZero m] in
theorem key_eq {Y : Type*}
    (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (post : Output branch root rows → Y) (side : CanonicalKeys.Side) :
    CanonicalKeys.key side (TreeCanonical.numberedSlots
        (leftSlots rows repeats p outside clauses designated x))
      (WholeCutKeyLocality.query rows repeats p
        (leftSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.leftTape rows repeats p outside placeholder clauses designated x external) post) =
    CanonicalKeys.key side (TreeCanonical.numberedSlots
        (rightSlots rows repeats p outside clauses designated x))
      (WholeCutKeyLocality.query rows repeats p
        (rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated x external) post) := by
  rw [query_pullback]
  exact CanonicalKeys.key_projection side
    (TreeCanonical.numberedProjection (projection rows repeats p outside clauses designated x)) _

omit [NeZero m] in
theorem label_val_eq {Y : Type*}
    (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (post : Output branch root rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch root t))
    (side : CanonicalKeys.Side) :
    (KeyStrategy.label labeling side (TreeCanonical.numberedSlots
        (leftSlots rows repeats p outside clauses designated x))
      (WholeCutKeyLocality.query rows repeats p
        (leftSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.leftTape rows repeats p outside placeholder clauses designated x external) post)).val =
    (KeyStrategy.label labeling side (TreeCanonical.numberedSlots
        (rightSlots rows repeats p outside clauses designated x))
      (WholeCutKeyLocality.query rows repeats p
        (rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated x external) post)).val :=
  KeyStrategy.label_val_eq_of_key_eq labeling side side _ _ _ _
    (key_eq rows repeats p outside placeholder clauses designated x external post side)

omit [NeZero m] in
theorem response_eq {Y : Type*}
    (x : Sample (t := t) rows repeats p clauses designated)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (post : Output branch root rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch root t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots
        (leftSlots rows repeats p outside clauses designated x))
      (WholeCutKeyLocality.query rows repeats p
        (leftSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.leftTape rows repeats p outside placeholder clauses designated x external) post) =
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots
        (rightSlots rows repeats p outside clauses designated x))
      (WholeCutKeyLocality.query rows repeats p
        (rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated x external) post) := by
  rw [query_pullback]
  exact KeyStrategy.response_projection labeling side
    (TreeCanonical.numberedProjection (projection rows repeats p outside clauses designated x)) _

end
end PerfectCompleteness.CleanPhysicalCanonicalQuery

end

end OAI
