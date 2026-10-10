import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Foundations.KeyFiniteness
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas
import OAI.Computability.PerfectCompleteness.Sampling.PreliminarySampler

namespace OAI


namespace PerfectCompleteness.MetadataFreeSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open scoped Classical

noncomputable section

abbrev SignTuple (branch : Nat → Nat) (n t : Nat) :=
  Slots branch n → Fin t → SourceClause.Triple

abbrev EncodedAssignment (branch : Nat → Nat) (n t : Nat) :=
  Slots branch n → Fin t → Fin 7

variable {branch : Nat → Nat} {n t : Nat}

abbrev SignedLeaf (signs : SignTuple branch n t) (leaf : Slots branch n) :=
  (k : Fin t) → ClauseSupport.Answer (signs leaf k)

abbrev SignedDomain (signs : SignTuple branch n t) := Assignment (SignedLeaf signs)

abbrev SignedH (signs : SignTuple branch n t) :
    Submodule F2 (SignedDomain signs → F2) :=
  space F2 branch n (SignedLeaf signs)

def nodeSigns (signs : SignTuple branch n t) (node : Nodes branch n) :
    SignTuple branch (Nodes.height node) t :=
  fun leaf k => signs ((Nodes.path node).slotEmbedding leaf) k

abbrev SignedArrays (signs : SignTuple branch n t) (rows : Nat → Nat) :=
  (node : Nodes branch n) → Fin (rows (Nodes.height node)) → SignedH (nodeSigns signs node)

def assignmentEquiv (signs : SignTuple branch n t) :
    SignedDomain signs ≃ EncodedAssignment branch n t :=
  Equiv.piCongrRight (fun leaf => Equiv.piCongrRight (fun k =>
    CanonicalKeys.answerEquivFinSeven (signs leaf k)))

abbrev ArrayTables (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :=
  (node : Nodes branch n) → Fin (rows (Nodes.height node)) →
    EncodedAssignment branch n t → F2

abbrev Input (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :=
  SignTuple branch n t × ArrayTables branch n t rows

instance inputFintype (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) :
    Fintype (Input branch n t rows) := by
  unfold Input ArrayTables SignTuple EncodedAssignment
  infer_instance

def tableJoint {rows : Nat → Nat} (tables : ArrayTables branch n t rows)
    (x : EncodedAssignment branch n t) : Output branch n rows :=
  (fun node row => tables node row x, PUnit.unit)

section Source

variable {v m : Nat}

def sourceSigns (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) : SignTuple branch n t :=
  fun leaf k => (clauses (q leaf k)).signs

abbrev sourceSlots (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :=
  HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)

theorem sourceLeaf_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :
    LeafDomain (sourceSlots clauses q) = SignedLeaf (sourceSigns clauses q) := rfl

theorem sourceDomain_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :
    Domain (sourceSlots clauses q) = SignedDomain (sourceSigns clauses q) := rfl

theorem sourceH_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :
    H (sourceSlots clauses q) = SignedH (sourceSigns clauses q) := rfl

theorem sourceNodeH_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) (node : Nodes branch n) :
    H (nodeSlots (sourceSlots clauses q) node) =
      SignedH (nodeSigns (sourceSigns clauses q) node) := rfl

theorem sourceArrays_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) (rows : Nat → Nat) :
    Arrays (sourceSlots clauses q) rows = SignedArrays (sourceSigns clauses q) rows := rfl

def sourceAssignmentEquiv (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :
    Domain (sourceSlots clauses q) ≃ EncodedAssignment branch n t :=
  assignmentEquiv (sourceSigns clauses q)

def numberedAssignmentEquiv (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) :
    MixedSupport.Assignment (TreeCanonical.numberedSlots (sourceSlots clauses q)) ≃
      EncodedAssignment branch n t :=
  (TreeCanonical.assignmentEquiv (sourceSlots clauses q)).symm.trans
    (sourceAssignmentEquiv clauses q)

def encodeArrays (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
    (arrays : Arrays (sourceSlots clauses q) rows) : ArrayTables branch n t rows :=
  fun node row x => joint arrays ((sourceAssignmentEquiv clauses q).symm x) node row

theorem tableJoint_encodeArrays (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
    (arrays : Arrays (sourceSlots clauses q) rows) (x : EncodedAssignment branch n t) :
    tableJoint (encodeArrays clauses q arrays) x =
      fullJoint arrays ((sourceAssignmentEquiv clauses q).symm x) := rfl

theorem tableJoint_at_assignment (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
    (arrays : Arrays (sourceSlots clauses q) rows) (x : Domain (sourceSlots clauses q)) :
    tableJoint (encodeArrays clauses q arrays) (sourceAssignmentEquiv clauses q x) =
      fullJoint arrays x := by
  rw [tableJoint_encodeArrays, Equiv.symm_apply_apply]

theorem numberedFunction_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
    (arrays : Arrays (sourceSlots clauses q) rows) :
    TreeCanonical.numberedFunction (sourceSlots clauses q) (fullJoint arrays) =
      tableJoint (encodeArrays clauses q arrays) ∘ numberedAssignmentEquiv clauses q := by
  funext x
  exact (tableJoint_at_assignment clauses q arrays
    ((TreeCanonical.assignmentEquiv (sourceSlots clauses q)).symm x)).symm

def encodeInput (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
    (arrays : Arrays (sourceSlots clauses q) rows) : Input branch n t rows :=
  (sourceSigns clauses q, encodeArrays clauses q arrays)

def encodeTape (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) (rows repeats : Nat → Nat)
    {d : Nat} (p : Path branch n d)
    (tape : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)) :
    Input branch n t rows :=
  encodeInput clauses q (WholeArraySampler.evaluate rows repeats p (sourceSlots clauses q) tape)

theorem numberedFunction_encodeTape (clauses : Fin m → SourceClause.NormalizedClause v)
    (q : PreliminarySampler.Questions branch n t m) (rows repeats : Nat → Nat)
    {d : Nat} (p : Path branch n d)
    (tape : WholeArraySampler.Tape rows repeats p (sourceSlots clauses q)) :
    TreeCanonical.numberedFunction (sourceSlots clauses q)
        (fullJoint (WholeArraySampler.evaluate rows repeats p (sourceSlots clauses q) tape)) =
      tableJoint (encodeTape clauses q rows repeats p tape).2 ∘ numberedAssignmentEquiv clauses q :=
  numberedFunction_eq clauses q _

end Source

def outputEquiv (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) :
    Output branch n rows ≃ Fin (Fintype.card (Output branch n rows)) :=
  Fintype.equivFin _

def numberedShapes (signs : SignTuple branch n t) :
    Fin (TreeCanonical.locationCount branch n t) → CanonicalKeyShape.Shape :=
  fun j => .clause (signs ((TreeCanonical.numbering branch n t).symm j).1
    ((TreeCanonical.numbering branch n t).symm j).2)

def dummyTreeSlots (signs : SignTuple branch n t) :
    Slots branch n → Fin t → MixedSupport.Slot :=
  fun leaf k => CanonicalKeyShape.dummy (.clause (signs leaf k))

def dummyNumberedEquiv (signs : SignTuple branch n t) :
    MixedSupport.Assignment (CanonicalKeyShape.dummySlots (numberedShapes signs)) ≃
      EncodedAssignment branch n t :=
  (TreeCanonical.assignmentEquiv (dummyTreeSlots signs)).symm.trans (assignmentEquiv signs)

def shapeInput {rows : Nat → Nat} (data : Input branch n t rows) :
    CanonicalKeyShape.Input (TreeCanonical.locationCount branch n t)
      (Fintype.card (Output branch n rows)) :=
  ⟨numberedShapes data.1,
    fun x => outputEquiv branch n rows (tableJoint data.2 (dummyNumberedEquiv data.1 x))⟩


variable {v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (q : PreliminarySampler.Questions branch n t m) {rows : Nat → Nat}
  (arrays : Arrays (sourceSlots clauses q) rows)

theorem shapeInput_encodeInput :
    shapeInput (encodeInput clauses q arrays) =
      CanonicalKeyShape.input (TreeCanonical.numberedSlots (sourceSlots clauses q))
        (outputEquiv branch n rows ∘
          TreeCanonical.numberedFunction (sourceSlots clauses q) (fullJoint arrays)) := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext x
    change outputEquiv branch n rows
        (fullJoint arrays ((sourceAssignmentEquiv clauses q).symm
          (sourceAssignmentEquiv clauses q
            ((TreeCanonical.assignmentEquiv (sourceSlots clauses q)).symm x)))) =
      outputEquiv branch n rows
        (fullJoint arrays ((TreeCanonical.assignmentEquiv (sourceSlots clauses q)).symm x))
    rw [Equiv.symm_apply_apply]

theorem shapeInput_partition :
    CanonicalKeyShape.inputPartition (shapeInput (encodeInput clauses q arrays)) =
      CanonicalKeys.partition (TreeCanonical.numberedSlots (sourceSlots clauses q))
        (TreeCanonical.numberedFunction (sourceSlots clauses q) (fullJoint arrays)) := by
  rw [shapeInput_encodeInput, CanonicalKeyShape.inputPartition_eq]
  apply CanonicalKeys.partition_kernel_invariant
  intro x y
  exact (outputEquiv branch n rows).injective.eq_iff

theorem shapeInput_retained :
    CanonicalKeyShape.retained (TreeCanonical.numberedSlots (sourceSlots clauses q))
        (CanonicalKeyShape.inputModes (shapeInput (encodeInput clauses q arrays))) =
      MixedSupport.retainedKeys (TreeCanonical.numberedSlots (sourceSlots clauses q))
        (TreeCanonical.numberedFunction (sourceSlots clauses q) (fullJoint arrays)) := by
  rw [shapeInput_encodeInput, CanonicalKeyShape.inputModes_recover]
  apply MixedSupport.retainedKeys_kernel_invariant
  intro x y
  exact (outputEquiv branch n rows).injective.eq_iff

end
end PerfectCompleteness.MetadataFreeSampler

end OAI
