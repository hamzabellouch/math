import Mathlib

namespace OAI

noncomputable section
open Set

namespace WeakMTWTransport

lemma finite_simplex_representation {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ m : ℕ, 0 < m ∧ m ≤ Module.finrank ℝ E + 1 ∧
      ∃ z : Fin m → E, ∃ w : Fin m → ℝ,
        (∀ i, z i ∈ S) ∧ (∀ i, 0 ≤ w i) ∧
        (∑ i, w i = 1) ∧ (∑ i, w i • z i = x) := by
  classical
  obtain ⟨ι,inst,z,w,hz,hi,hw,hsum,heq⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let : Fintype ι := inst
  have : Nonempty ι := by
    by_contra h
    have : IsEmpty ι := not_nonempty_iff.mp h
    simp at hsum
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι,Fintype.card_pos,
    hi.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1),
    fun i => z (e.symm i),fun i => w (e.symm i),?_,?_,?_,?_⟩
  · intro i
    exact hz (mem_range_self _)
  · intro i
    exact (hw _).le
  · simpa only [e.symm.sum_comp] using hsum
  · exact (e.symm.sum_comp (fun i => w i • z i)).trans heq

end WeakMTWTransport

end

end OAI
