import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingCompiled

namespace OAI

/-! Filtering the bond tape retains exactly the unselected physical edges,
including their orientation, regardless of their list order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingSelectProgram
open QuantumCrossingListBlock
open scoped Classical

variable {G : QMARationalExchangeGraph} {r m : ℕ}
    (S : QMARationalCrossingSelection G r) (labels : G.Edge ≃ Fin m)
    (htag : ∀ e i a, S.tag e=some (i,a) ↔ G.CrossingMatch S.site e (i,a))

include htag in
theorem retained_edge_source (e : (retainedGraph S labels).Edge) :
    ∃ f : S.retained.Edge,
      (retainedGraph S labels).left e = S.retained.left f ∧
      (retainedGraph S labels).right e = S.retained.right f := by
  let xs := retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels)
  have hm : xs.get e ∈ xs := List.get_mem xs e
  obtain ⟨hm,hk⟩ := List.mem_filter.mp hm
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  have ht : S.tag (labels.symm i)=none := by
    rw [← hi] at hk
    exact of_decide_eq_true ((keep_selected S htag (labels.symm i)).symm.trans hk)
  refine ⟨⟨labels.symm i,ht⟩,?_,?_⟩
  · apply Fin.ext
    change (xs.get e).1=(G.left (labels.symm i)).val
    rw [← hi]
  · apply Fin.ext
    change (xs.get e).2.1=(G.right (labels.symm i)).val
    rw [← hi]

include htag in
theorem retained_edge_target (f : S.retained.Edge) :
    ∃ e : (retainedGraph S labels).Edge,
      (retainedGraph S labels).left e = S.retained.left f ∧
      (retainedGraph S labels).right e = S.retained.right f := by
  let b : MediatorListProgram.Bond := ((G.left f.val).val,(G.right f.val).val,G.weight f.val)
  let xs := retained (pairs (List.ofFn (encodedSites S.site)),QuantumListGraph.packed G labels)
  have hm : b ∈ xs := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_ofFn.mpr ⟨labels f.val,?_⟩,?_⟩
    · simp only [Equiv.symm_apply_apply]
      rfl
    · exact (keep_selected S htag f.val).trans (decide_eq_true f.property)
  obtain ⟨e,he⟩ := List.mem_iff_get.mp hm
  refine ⟨e,?_,?_⟩
  · apply Fin.ext
    change (xs.get e).1=(G.left f.val).val
    rw [he]
  · apply Fin.ext
    change (xs.get e).2.1=(G.right f.val).val
    rw [he]

end ContinuumCoulomb.QuantumCrossingSelectProgram

end

end OAI
