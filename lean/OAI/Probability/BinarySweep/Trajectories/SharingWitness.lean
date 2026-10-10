import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
variable {I H : Type*} [Fintype I] [Fintype H] [DecidableEq I]

theorem sharing_witness (G : SimpleGraph I) (R : I → H → Prop) :
    let S := Finset.univ.filter (fun i => (∃ j, G.Adj i j) ∨ ∃ h, R i h)
    ∃ T : Finset I, T ⊆ S ∧ S.card ≤ 2*T.card ∧
      ∀ i ∈ T, (∃ j, j ∉ T ∧ G.Adj i j) ∨ ∃ h, R i h := by
  classical
  intro S
  obtain ⟨A,hA⟩ := G.maximumIndepSet_exists
  have hm := hA.isMaximalIndepSet A
  have hi := (G.isIndepSet_iff).mp hm.1
  have hn (i : I) (hiA : i ∉ A) : ∃ j ∈ A, G.Adj i j := by
    by_contra! h
    have hins : G.IsIndepSet (insert i (A : Set I)) := by
      apply G.isIndepSet_iff.mpr
      intro x hx y hy hxy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact (hxy rfl).elim
      · exact h y hy
      · exact fun hadj => h x hx hadj.symm
      · exact hi hx hy hxy
    have hj := hm.2 hins (Set.subset_insert i (A : Set I)) (Set.mem_insert i (A : Set I))
    exact hiA hj
  have hcard := Finset.card_sdiff_add_card_inter S A
  by_cases hc : (S \ A).card ≤ (S ∩ A).card
  · refine ⟨S ∩ A,Finset.inter_subset_left,by omega,?_⟩
    intro i hiT
    obtain ⟨hiS, hiA⟩ := Finset.mem_inter.mp hiT
    obtain hiS | hiS := (Finset.mem_filter.mp hiS).2
    · obtain ⟨j,hij⟩ := hiS
      refine Or.inl ⟨j,?_,hij⟩
      intro hj
      exact hi hiA (Finset.mem_inter.mp hj).2 (G.ne_of_adj hij) hij
    · exact Or.inr hiS
  · refine ⟨S \ A,Finset.sdiff_subset,by omega,?_⟩
    intro i hiT
    obtain ⟨j,hj,hij⟩ := hn i (Finset.mem_sdiff.mp hiT).2
    exact Or.inl ⟨j,fun hjT => (Finset.mem_sdiff.mp hjT).2 hj,hij⟩

end BinaryCoordinateSweeps.Sparse

end

end OAI
