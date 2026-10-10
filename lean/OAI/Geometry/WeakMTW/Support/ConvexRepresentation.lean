import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set
open scoped BigOperators
namespace ConvexRepresentation
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem fixed_size {S : Set E} {x : E} (hx : x ∈ convexHull ℝ S) {N : ℕ}
    (hN : Module.finrank ℝ E + 1 ≤ N) :
    ∃ (z : Fin N → E) (w : Fin N → ℝ), (∀ i, z i ∈ S) ∧
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • z i = x := by
  classical
  let T := Caratheodory.minCardFinsetOfMemConvexHull hx
  have hTS : (T : Set E) ⊆ S := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hTx : x ∈ convexHull ℝ (T : Set E) := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  have hTI := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hTN : Fintype.card T ≤ N := hTI.card_le_finrank_succ.trans
    ((Nat.add_le_add_right (Submodule.finrank_le _) 1).trans hN)
  obtain ⟨a₀,ha₀⟩ := Caratheodory.minCardFinsetOfMemConvexHull_nonempty hx
  have htcombo := hTx
  rw [Finset.convexHull_eq] at htcombo
  obtain ⟨v,hv,hvsum,hvx⟩ := htcombo
  have hvsum' : ∑ i : T, v i = 1 := by simpa only [Finset.univ_eq_attach,Finset.sum_attach] using hvsum
  have hvx' : ∑ i : T, v i • (i : E) = x := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hvsum] at hvx
    change (∑ i ∈ T.attach, (fun j : E => v j • j) (i : E)) = x
    rw [Finset.sum_attach (f := fun j : E => v j • j)]
    exact hvx
  obtain ⟨e⟩ : Nonempty (T ↪ Fin N) := Function.Embedding.nonempty_of_card_le (by simpa using hTN)
  let z : Fin N → E := Function.extend e (fun i : T => (i : E)) (fun _ => a₀)
  let w : Fin N → ℝ := Function.extend e (fun i : T => v i) (fun _ => 0)
  have hz (i : T) : z (e i) = (i : E) := e.injective.extend_apply _ _ i
  have hw (i : T) : w (e i) = v i := e.injective.extend_apply _ _ i
  have hwzero (i : Fin N) (hi : i ∉ range e) : w i = 0 := Function.extend_apply' _ _ _ hi
  refine ⟨z,w,?_,?_,?_,?_⟩
  · intro i
    by_cases hi : i ∈ range e
    · obtain ⟨j,rfl⟩ := hi
      rw [hz]
      exact hTS j.2
    · have hi' : z i = a₀ := Function.extend_apply' _ _ _ hi
      rw [hi']
      exact hTS ha₀
  · intro i
    by_cases hi : i ∈ range e
    · obtain ⟨j,rfl⟩ := hi
      rw [hw]
      exact hv j j.2
    · rw [hwzero i hi]
  · rw [← hvsum']
    symm
    exact Fintype.sum_of_injective e e.injective _ w (fun i hi => hwzero i hi) (fun i => (hw i).symm)
  · rw [← hvx']
    symm
    apply Fintype.sum_of_injective e e.injective
    · intro i hi
      rw [hwzero i hi,zero_smul]
    · intro i
      rw [hw,hz]

end
end ConvexRepresentation
end

end WeakMTWGlobalSupport

end OAI
