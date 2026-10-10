import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortRankProgram

namespace OAI

/-! The literal incidence count computes the very arm assignment used by the
spatial routing proof, for any explicit enumeration of the interaction labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPortRankProgram
open scoped Classical

def entries {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (i : Fin m) : Entry :=
  ((M.left (labels.symm i)).val,
    (M.right (labels.symm i)).val,(M.laneColor (labels.symm i)).val)

theorem value_actual {A B : ℕ} (M : QMASpatialExchangeModel A B) {m : ℕ}
    (labels : M.Term ≃ Fin m) (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    value ((v.val,(M.laneColor e.val).val),List.ofFn (entries M labels)) =
      ((M.endpointPorts hd v).assign e).val := by
  rw [count_ofFn,M.endpointPorts_assign_rank hA]
  symm
  apply Finset.card_bij (fun f _ => labels f.val)
  · intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [entries,labels.symm_apply_apply]
    refine ⟨?_,(Finset.mem_filter.mp hf).2⟩
    rcases f.property with hl | hr
    · exact Or.inl (congrArg Fin.val hl)
    · exact Or.inr (congrArg Fin.val hr)
  · intro f hf g hg h
    exact Subtype.ext (labels.injective h)
  · intro i hi
    obtain ⟨_,hinc,hlt⟩ := Finset.mem_filter.mp hi
    dsimp only [entries] at hinc hlt
    have hmember : M.left (labels.symm i)=v ∨ M.right (labels.symm i)=v :=
      hinc.imp Fin.ext Fin.ext
    let f : M.Incident v := ⟨labels.symm i,hmember⟩
    refine ⟨f,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩,?_⟩
    exact labels.apply_symm_apply i

end ContinuumCoulomb.QuantumPortRankProgram

end

end OAI
