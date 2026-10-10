import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-!
# Finite partitions by a key

The fibers indexed by the image of a finite source partition that source.
Filtering the source commutes with taking fibers, so the same partition
identities apply to restrictions of a weighted sum.
-/

namespace TalagrandDiscreteConvexity.FiniteFibers

open scoped BigOperators

variable {α β M : Type*} [DecidableEq β]

/-- The elements of `A` with the specified key. -/
def fiber (A : Finset α) (key : α → β) (b : β) : Finset α :=
  A.filter (fun a => key a = b)

/-- Exactly the keys attained by the finite source. -/
def keys (A : Finset α) (key : α → β) : Finset β :=
  A.image key

@[simp]
theorem mem_fiber {A : Finset α} {key : α → β} {b : β} {a : α} :
    a ∈ fiber A key b ↔ a ∈ A ∧ key a = b :=
  Finset.mem_filter

@[simp]
theorem mem_keys {A : Finset α} {key : α → β} {b : β} :
    b ∈ keys A key ↔ ∃ a ∈ A, key a = b :=
  Finset.mem_image

theorem fiber_subset (A : Finset α) (key : α → β) (b : β) :
    fiber A key b ⊆ A :=
  Finset.filter_subset _ _

theorem key_eq_of_mem_fiber {A : Finset α} {key : α → β} {b : β} {a : α}
    (ha : a ∈ fiber A key b) : key a = b :=
  (mem_fiber.mp ha).2

@[simp]
theorem fiber_nonempty_iff (A : Finset α) (key : α → β) (b : β) :
    (fiber A key b).Nonempty ↔ b ∈ keys A key := by
  simp only [fiber, Finset.filter_nonempty_iff, mem_keys]

/-- Restricting the source commutes with taking a fiber. -/
theorem filter_fiber (A : Finset α) (key : α → β) (b : β)
    (P : α → Prop) [DecidablePred P] :
    fiber (A.filter P) key b = (fiber A key b).filter P :=
  Finset.filter_comm P (fun a => key a = b) A

variable [AddCommMonoid M]

/-- Summing the fibers over the attained keys counts each source element once. -/
theorem sum_fibers (A : Finset α) (key : α → β) (f : α → M) :
    (∑ b ∈ keys A key, ∑ a ∈ fiber A key b, f a) = ∑ a ∈ A, f a := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun a ha => Finset.mem_image_of_mem key ha) f

/-- The same partition identity after restricting every fiber by a predicate. -/
theorem sum_filter_fibers (A : Finset α) (key : α → β)
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ b ∈ keys A key, ∑ a ∈ (fiber A key b).filter P, f a) =
      ∑ a ∈ A.filter P, f a := by
  calc
    (∑ b ∈ keys A key, ∑ a ∈ (fiber A key b).filter P, f a) =
        ∑ b ∈ keys A key, ∑ a ∈ fiber (A.filter P) key b, f a := by
      simp only [filter_fiber]
    _ = ∑ a ∈ A.filter P, f a := by
      exact Finset.sum_fiberwise_of_maps_to
        (fun a ha => Finset.mem_image_of_mem key (Finset.mem_filter.mp ha).1) f

/-- A restricted sum decomposed into the bins of the original source. -/
theorem sum_filter_eq_sum_fibers (A : Finset α) (key : α → β)
    (P : α → Prop) [DecidablePred P] (f : α → M) :
    (∑ a ∈ A.filter P, f a) =
      ∑ b ∈ keys A key, ∑ a ∈ (fiber A key b).filter P, f a :=
  (sum_filter_fibers A key P f).symm

end TalagrandDiscreteConvexity.FiniteFibers

end OAI
