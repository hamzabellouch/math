import Mathlib.Data.Fintype.Sum
import OAI.Computability.PerfectCompleteness.Construction.DescendantSpacesLemmas
import OAI.Computability.PerfectCompleteness.Construction.TreeCanonical
import OAI.Computability.PerfectCompleteness.Foundations.LinearEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Reduction.SourceCompleteness

namespace OAI


namespace PerfectCompleteness.HierarchicalArrays

open TreeSourceSpaces

def Nodes (branch : Nat → Nat) : Nat → Type
  | 0 => Empty
  | n + 1 => Unit ⊕ (Fin (branch n) × Nodes branch n)

instance nodesFintype (branch : Nat → Nat) (n : Nat) : Fintype (Nodes branch n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ n ih =>
      letI : Fintype (Nodes branch n) := ih
      exact inferInstanceAs (Fintype (Unit ⊕ (Fin (branch n) × Nodes branch n)))

instance nodesDecidableEq (branch : Nat → Nat) (n : Nat) :
    DecidableEq (Nodes branch n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ n ih =>
      letI : DecidableEq (Nodes branch n) := ih
      exact inferInstanceAs (DecidableEq (Unit ⊕ (Fin (branch n) × Nodes branch n)))

namespace Nodes

variable {branch : Nat → Nat}

def height : {n : Nat} → Nodes branch n → Nat
  | 0, node => nomatch node
  | n + 1, .inl _ => n + 1
  | _ + 1, .inr (_, node) => height node

def path : {n : Nat} → (node : Nodes branch n) →
    DescendantSpaces.Path branch n (height node)
  | 0, node => nomatch node
  | n + 1, .inl _ => .refl (n + 1)
  | _ + 1, .inr (i, node) => .step i (path node)

theorem height_pos : ∀ {n : Nat} (node : Nodes branch n), 0 < height node := by
  intro n
  induction n with
  | zero =>
      intro node
      exact nomatch node
  | succ n ih =>
      intro node
      cases node with
      | inl _ => exact Nat.zero_lt_succ n
      | inr pair => exact ih pair.2

theorem height_le {n : Nat} (node : Nodes branch n) : height node ≤ n :=
  (path node).height_le

end Nodes

variable {branch : Nat → Nat} {n t : Nat}

def nodeSlots (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) : RecursiveSpaces.Slots branch (Nodes.height node) →
      Fin t → MixedSupport.Slot :=
  fun s => slots ((Nodes.path node).slotEmbedding s)

def restrictNode (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) : Domain slots → Domain (nodeSlots slots node) :=
  (Nodes.path node).restriction (LeafDomain slots)

theorem restrictNode_surjective
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (node : Nodes branch n) : Function.Surjective (restrictNode slots node) :=
  (Nodes.path node).restriction_surjective (LeafDomain slots) (fun _ => inferInstance)

abbrev Block (rows : Nat → Nat) (node : Nodes branch n) := Fin (rows (Nodes.height node)) → F2

abbrev Arrays (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :=
  ∀ node : Nodes branch n, Fin (rows (Nodes.height node)) → H (nodeSlots slots node)

theorem arrays_finite
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) (rows : Nat → Nat) :
    Finite (Arrays slots rows) := by
  infer_instance

def joint {slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    {rows : Nat → Nat} (arrays : Arrays slots rows) :
    Domain slots → ∀ node : Nodes branch n, Block rows node :=
  fun x node row => (arrays node row).val (restrictNode slots node x)

@[simp] theorem joint_component
    {slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    {rows : Nat → Nat} (arrays : Arrays slots rows) (x : Domain slots)
    (node : Nodes branch n) (row : Fin (rows (Nodes.height node))) :
    joint arrays x node row = (arrays node row).val (restrictNode slots node x) := rfl

theorem row_mem_root
    {slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    {rows : Nat → Nat} (arrays : Arrays slots rows)
    (hbranch : ∀ k < n, 0 < branch k) (node : Nodes branch n)
    (row : Fin (rows (Nodes.height node))) :
    (fun x => joint arrays x node row) ∈ H slots :=
  DescendantSpaces.space_descendant_le (Nodes.path node) (LeafDomain slots) hbranch
    (Submodule.mem_map_of_mem (arrays node row).property)

abbrev Output (branch : Nat → Nat) (n : Nat) (rows : Nat → Nat) : Type :=
  BlockQuotient.JointOutput (fun node : Nodes branch n => Block rows node) PUnit

def fullJoint {slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    {rows : Nat → Nat} (arrays : Arrays slots rows) : Domain slots → Output branch n rows :=
  fun x => (joint arrays x, PUnit.unit)

variable {v m : Nat}

def sourceSlots (clauses : Fin m → SourceClause.NormalizedClause v)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m) :
    RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
  fun s k => SourceKeys.slot clauses (endpoints s k)

noncomputable section

def numberedEndpoints
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m) :
    Fin (TreeCanonical.locationCount branch n t) → SourceKeys.Endpoint v m :=
  fun j => endpoints ((TreeCanonical.numbering branch n t).symm j).1
    ((TreeCanonical.numbering branch n t).symm j).2

theorem numberedSlots_sourceSlots (clauses : Fin m → SourceClause.NormalizedClause v)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m) :
    TreeCanonical.numberedSlots (sourceSlots clauses endpoints) =
      SourceKeys.slot clauses ∘ numberedEndpoints endpoints := rfl

def presentation (clauses : Fin m → SourceClause.NormalizedClause v)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m)
    (rows : Nat → Nat) (arrays : Arrays (sourceSlots clauses endpoints) rows) :
    SourceCompleteness.Presentation clauses (TreeCanonical.locationCount branch n t)
      (Output branch n rows) where
  endpoints := numberedEndpoints endpoints
  joint := TreeCanonical.numberedFunction (sourceSlots clauses endpoints) (fullJoint arrays)

theorem presentation_key (side : CanonicalKeys.Side)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m)
    (rows : Nat → Nat) (arrays : Arrays (sourceSlots clauses endpoints) rows) :
    SourceCompleteness.presentationKey side (presentation clauses endpoints rows arrays) =
      TreeCanonical.key side (sourceSlots clauses endpoints) (fullJoint arrays) := rfl

theorem presentation_evaluate (clauses : Fin m → SourceClause.NormalizedClause v)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m)
    (rows : Nat → Nat) (arrays : Arrays (sourceSlots clauses endpoints) rows)
    (x : Domain (sourceSlots clauses endpoints)) :
    (presentation clauses endpoints rows arrays).joint
        (TreeCanonical.assignmentEquiv (sourceSlots clauses endpoints) x) = fullJoint arrays x :=
  congrArg (fullJoint arrays)
    ((TreeCanonical.assignmentEquiv (sourceSlots clauses endpoints)).symm_apply_apply x)

def sourceAssignment (clauses : Fin m → SourceClause.NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m) :
    Domain (sourceSlots clauses endpoints) :=
  fun s k => SourceKeys.endpointValue clauses assignment hsat (endpoints s k)

theorem sourceAssignment_numbered (clauses : Fin m → SourceClause.NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m) :
    TreeCanonical.assignmentEquiv (sourceSlots clauses endpoints)
        (sourceAssignment clauses assignment hsat endpoints) =
      SourceKeys.realizingAssignment clauses assignment hsat (numberedEndpoints endpoints) := rfl

theorem presentation_realizing (clauses : Fin m → SourceClause.NormalizedClause v)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true)
    (endpoints : RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m)
    (rows : Nat → Nat) (arrays : Arrays (sourceSlots clauses endpoints) rows) :
    (presentation clauses endpoints rows arrays).joint
        (SourceKeys.realizingAssignment clauses assignment hsat (numberedEndpoints endpoints)) =
      fullJoint arrays (sourceAssignment clauses assignment hsat endpoints) := by
  rw [← sourceAssignment_numbered]
  exact presentation_evaluate clauses endpoints rows arrays _

end

end PerfectCompleteness.HierarchicalArrays

end OAI
