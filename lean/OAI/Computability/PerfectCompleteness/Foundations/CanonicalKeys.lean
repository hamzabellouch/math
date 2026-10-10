import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.PerfectCompleteness.Foundations.ReducedDomains

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport

variable {n : Nat} {Y : Type*}

inductive Side where
  | left
  | right
  deriving DecidableEq

structure Key (n : Nat) where
  side : Side
  retained : List (Fin n × SlotKey)
  partition : Set (Set (Fin n → ReducedValue))

noncomputable def partition (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Set (Set (Fin n → ReducedValue)) :=
  ReducedPartition.parts (reduction slots f) f

noncomputable def key (side : Side) (slots : Fin n → Slot)
    (f : Assignment slots → Y) : Key n :=
  ⟨side, retainedKeys slots f, partition slots f⟩

theorem constantOnFibers (slots : Fin n → Slot) (f : Assignment slots → Y) :
    ReducedPartition.ConstantOnFibers (reduction slots f) f := by
  intro x x' h
  exact constant_on_reduction_fibers slots f h

theorem covered_iff_legal (slots : Fin n → Slot) (f : Assignment slots → Y)
    (values : Fin n → ReducedValue) :
    (∃ P ∈ partition slots f, values ∈ P) ↔
      values ∈ ReducedDomains.legalAssignments (keyFields slots f) := by
  rw [← ReducedDomains.range_reduction slots f]
  exact ReducedPartition.covered_iff_mem_range (reduction slots f) f values

theorem legal_domain_projection {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    ReducedDomains.legalAssignments (keyFields slots (f ∘ projectionMap p)) =
      ReducedDomains.legalAssignments (keyFields projected f) := by
  rw [keyFields_projection]

theorem partition_projection {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    partition slots (f ∘ projectionMap p) = partition projected f := by
  exact ReducedPartition.parts_eq_of_pullback
    (projectionMap p) (projectionMap_surjective p)
    (reduction slots (f ∘ projectionMap p)) (reduction projected f)
    (f ∘ projectionMap p) f (reduction_projection p f) (fun _ => rfl)

theorem key_projection (side : Side) {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    key side slots (f ∘ projectionMap p) = key side projected f := by
  simp only [key, retainedKeys_projection, partition_projection]

abbrev Label (slots : Fin n → Slot) (f : Assignment slots → Y) :=
  ReducedPartition.Part (reduction slots f) f

noncomputable def evaluateLabel (slots : Fin n → Slot) (f : Assignment slots → Y)
    (x : Assignment slots) : Label slots f :=
  ReducedPartition.label (reduction slots f) f x

noncomputable def restore (slots : Fin n → Slot) (f : Assignment slots → Y)
    (P : Label slots f) : Y :=
  ReducedPartition.output (reduction slots f) f P

@[simp] theorem restore_evaluateLabel (slots : Fin n → Slot)
    (f : Assignment slots → Y) (x : Assignment slots) :
    restore slots f (evaluateLabel slots f x) = f x :=
  ReducedPartition.output_label (reduction slots f) f (constantOnFibers slots f) x

theorem restore_injective (slots : Fin n → Slot) (f : Assignment slots → Y) :
    Function.Injective (restore slots f) :=
  ReducedPartition.output_injective (reduction slots f) f

noncomputable def transportLabel {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y)
    (P : Label slots (f ∘ projectionMap p)) : Label projected f :=
  ⟨P.val, by
    change P.val ∈ partition projected f
    rw [← partition_projection p f]
    exact P.property⟩

theorem transportLabel_bijective {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    Function.Bijective (transportLabel p f) := by
  constructor
  · intro P Q h
    exact Subtype.ext (congrArg (fun R : Label projected f => R.val) h)
  · intro Q
    have hQ : Q.val ∈ partition slots (f ∘ projectionMap p) := by
      rw [partition_projection p f]
      exact Q.property
    exact ⟨⟨Q.val, hQ⟩, Subtype.ext rfl⟩

theorem evaluateLabel_projection {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y)
    (x : Assignment slots) :
    transportLabel p f (evaluateLabel slots (f ∘ projectionMap p) x) =
      evaluateLabel projected f (projectionMap p x) := by
  apply Subtype.ext
  exact ReducedPartition.fiber_eq_of_pullback
    (projectionMap p) (projectionMap_surjective p)
    (reduction slots (f ∘ projectionMap p)) (reduction projected f)
    (f ∘ projectionMap p) f (reduction_projection p f) (fun _ => rfl) x

theorem restore_projection {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y)
    (P : Label slots (f ∘ projectionMap p)) :
    restore slots (f ∘ projectionMap p) P =
      restore projected f (transportLabel p f P) := by
  exact ReducedPartition.output_eq_of_shared_part
    (projectionMap p) (reduction slots (f ∘ projectionMap p)) (reduction projected f)
    (f ∘ projectionMap p) f (reduction_projection p f) (fun _ => rfl)
    (constantOnFibers projected f) P (transportLabel p f P) rfl

end PerfectCompleteness.CanonicalKeys

end

end OAI
