import OAI.GroupTheory.PolycyclicRecognition.Algebra.RingTraceProjectivity
import Mathlib.Data.Set.Finite.Powerset

namespace OAI

/-! # The ring of integer-valued functions on finite Boolean partitions

Only finitely many of the chosen Boolean coordinates may be used by any one
function. These functions form an actual subring, and each function has finite
range. This provides the small coefficient algebra needed for a countable group.
-/
noncomputable section
namespace PolycyclicRecognition
variable {X I : Type}

/-- A function is constant on the cells cut out by the indicated coordinates. -/
def DependsOnBoolean (a : I → X → Bool) (s : Finset I) (f : X → ℤ) : Prop :=
  ∀ x y, (∀ i ∈ s, a i x = a i y) → f x = f y

theorem DependsOnBoolean.mono {a : I → X → Bool} {s t : Finset I} {f : X → ℤ}
    (h : DependsOnBoolean a s f) (hst : s ⊆ t) : DependsOnBoolean a t f :=
  fun x y hxy => h x y (fun i hi => hxy i (hst hi))

def booleanStepRing (a : I → X → Bool) : Subring (X → ℤ) where
  carrier := {f | ∃ s : Finset I, DependsOnBoolean a s f}
  zero_mem' := ⟨∅, fun _ _ _ => rfl⟩
  one_mem' := ⟨∅, fun _ _ _ => rfl⟩
  neg_mem' := by
    rintro f ⟨s, hs⟩
    exact ⟨s, fun x y hxy => congrArg Neg.neg (hs x y hxy)⟩
  add_mem' := by
    classical
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, fun x y hxy => ?_⟩
    change f x + g x = f y + g y
    rw [hs.mono (Finset.subset_union_left) x y hxy,
      ht.mono (Finset.subset_union_right) x y hxy]
  mul_mem' := by
    classical
    rintro f g ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s ∪ t, fun x y hxy => ?_⟩
    change f x * g x = f y * g y
    rw [hs.mono (Finset.subset_union_left) x y hxy,
      ht.mono (Finset.subset_union_right) x y hxy]

theorem booleanStepRing_coordinate (a : I → X → Bool) (i : I) :
    (fun x => if a i x then (1 : ℤ) else 0) ∈ booleanStepRing a := by
  classical
  exact ⟨{i}, fun x y hxy => by
    dsimp only
    rw [hxy i (Finset.mem_singleton_self i)]⟩

def booleanPartitionCell (a : I → X → Bool) (s : Finset I) : Type :=
  Set.range (fun x : X => fun i : s => a i x)

def booleanPartitionPoint (a : I → X → Bool) (s : Finset I) (x : X) :
    booleanPartitionCell a s := ⟨fun i => a i x, ⟨x, rfl⟩⟩

instance (a : I → X → Bool) (s : Finset I) : Finite (booleanPartitionCell a s) := by
  dsimp [booleanPartitionCell]
  infer_instance

def booleanPartitionRepresentative (a : I → X → Bool) (s : Finset I)
    (c : booleanPartitionCell a s) : X := c.property.choose

theorem booleanPartitionPoint_representative (a : I → X → Bool) (s : Finset I)
    (c : booleanPartitionCell a s) :
    booleanPartitionPoint a s (booleanPartitionRepresentative a s c) = c := by
  apply Subtype.ext
  exact c.property.choose_spec

theorem dependsOnBoolean_factorization {a : I → X → Bool} {s : Finset I} {f : X → ℤ}
    (h : DependsOnBoolean a s f) :
    ∃ v : booleanPartitionCell a s → ℤ,
      f = fun x => v (booleanPartitionPoint a s x) := by
  refine ⟨fun c => f (booleanPartitionRepresentative a s c), ?_⟩
  funext x
  apply h
  intro i hi
  have he := congrArg (fun c : booleanPartitionCell a s => c.val ⟨i, hi⟩)
    (booleanPartitionPoint_representative a s (booleanPartitionPoint a s x))
  exact he.symm

theorem booleanStepRing_finite_range (a : I → X → Bool) (f : booleanStepRing a) :
    (Set.range (f : X → ℤ)).Finite := by
  obtain ⟨s, hs⟩ := f.property
  obtain ⟨v, hv⟩ := dependsOnBoolean_factorization hs
  rw [hv]
  exact (Set.finite_range v).subset (Set.range_comp_subset_range _ _)

end PolycyclicRecognition

end

end OAI
