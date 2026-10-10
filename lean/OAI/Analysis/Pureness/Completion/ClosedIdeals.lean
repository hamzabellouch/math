import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Sequences

namespace OAI
namespace CuntzPureness
open Filter Topology
variable {A : Type*} [NormedRing A]

def TopologicallySimple (A : Type*) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

def closedTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' (closure (I : Set A))
    (subset_closure I.zero_mem)
    (by
      intro x y hx hy
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (hux.add hvy)
        (Eventually.of_forall fun j => subset_closure (I.add_mem (hu j) (hv j))))
    (by
      intro x hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto hux.neg
        (Eventually.of_forall fun j => subset_closure (I.neg_mem (hu j))))
    (by
      intro x y hy
      obtain ⟨u, hu, huy⟩ := mem_closure_iff_seq_limit.mp hy
      exact isClosed_closure.mem_of_tendsto (huy.const_mul x)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_left x (u j) (hu j))))
    (by
      intro x y hx
      obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
      exact isClosed_closure.mem_of_tendsto (hux.mul_const y)
        (Eventually.of_forall fun j => subset_closure (I.mul_mem_right (u j) y (hu j))))

@[simp] theorem coe_closedTwoSidedIdeal (I : TwoSidedIdeal A) :
    (closedTwoSidedIdeal I : Set A) = closure (I : Set A) := by
  simp [closedTwoSidedIdeal]

theorem closure_span_singleton_eq_univ (hsimple : TopologicallySimple A)
    (h : A) (hh : h ≠ 0) :
    closure (TwoSidedIdeal.span {h} : Set A) = Set.univ := by
  let I : TwoSidedIdeal A := TwoSidedIdeal.span {h}
  have hclosed : IsClosed (closedTwoSidedIdeal I : Set A) := by
    rw [coe_closedTwoSidedIdeal]
    exact isClosed_closure
  have hmem : h ∈ closedTwoSidedIdeal I := by
    rw [← SetLike.mem_coe, coe_closedTwoSidedIdeal]
    exact subset_closure (TwoSidedIdeal.subset_span (Set.mem_singleton h))
  rcases hsimple (closedTwoSidedIdeal I) hclosed with hbot | htop
  · rw [hbot] at hmem
    exact (hh (by simpa using hmem)).elim
  · have heq := congrArg (fun J : TwoSidedIdeal A => (J : Set A)) htop
    simpa only [coe_closedTwoSidedIdeal, TwoSidedIdeal.coe_top] using heq
end CuntzPureness

end OAI
