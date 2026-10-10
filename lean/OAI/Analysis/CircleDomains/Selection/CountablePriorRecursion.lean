import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Countable

namespace OAI

/-! Recursive selection with every strict predecessor retained. The later
law construction instantiates this with a well-order whose initial segments
are countable, so all earlier laws are among its prescribed constraints. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

theorem exists_prior_compatible_family {I A : Type*} [LinearOrder I] [WellFoundedLT I]
    (P : ∀ i : I, (Iio i → A) → A → Prop)
    (hP : ∀ (i : I) (g : Iio i → A), ∃ a, P i g a) :
    ∃ f : I → A, ∀ i, P i (fun j => f j.val) (f i) := by
  let F (i : I) (g : ∀ j : I, j < i → A) : A :=
    Classical.choose (hP i (fun j => g j.val j.property))
  let f : I → A := WellFounded.fix wellFounded_lt F
  refine ⟨f, ?_⟩
  intro i
  have he : f i = F i (fun j _ => f j) := WellFounded.fix_eq wellFounded_lt F i
  rw [he]
  exact Classical.choose_spec (hP i (fun j => f j.val))

end CircleDomainRigidity

end

end OAI
