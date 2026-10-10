import OAI.Combinatorics.Ramsey.CycleClique.Construction.RestrictedLongest

namespace OAI

/-! Degree bounds when two deleted vertices are the only neighbours outside the longest path. -/

namespace CycleClique.Construction
theorem endpoint_neighbor_card_le {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x e : V} {W S : Finset V} {r : ℕ}
    (he : e ∈ pathEnds H x W r)
    (hS : ∀ v ∈ S, H.Adj e v ∧ v ∈ W) : S.card ≤ (pathEnds H x W r).card := by
  classical
  obtain ⟨f, hf, hlast⟩ := mem_pathEnds.mp he
  have hex : ∀ v : S, ∃ i : Fin r, f i.castSucc = v.val := by
    intro v
    obtain ⟨hadj, hvW⟩ := hS v.val v.property
    have hv : v.val ∈ Set.range f := by rw [hf.2.2.2]; exact hvW
    obtain ⟨j, hj⟩ := hv
    have hjlt : j.val < r := by
      have hneq : j ≠ Fin.last r := by
        intro heq
        subst j
        exact hadj.ne (hlast.symm.trans hj)
      have hval : j.val ≠ r := fun h => hneq (Fin.ext h)
      omega
    exact ⟨⟨j.val, hjlt⟩, by simpa using hj⟩
  let pivot : S → Fin r := fun v => Classical.choose (hex v)
  have hpivot : ∀ v : S, f (pivot v).castSucc = v.val := fun v => Classical.choose_spec (hex v)
  let suc : S → pathEnds H x W r := fun v =>
    ⟨f (pivot v).succ, successor_mem_pathEnds hf (pivot v) (by
      rw [hlast, hpivot]
      exact (hS v.val v.property).1)⟩
  have hinj : Function.Injective suc := by
    intro a b hab
    have hfin := hf.1 (congrArg Subtype.val hab)
    have hp : pivot a = pivot b := Fin.succ_injective r hfin
    apply Subtype.ext
    rw [← hpivot a, ← hpivot b, hp]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective suc hinj

theorem endpoint_degree_le_card_add_two {V : Type*} [Fintype V]
    {H : SimpleGraph V} {x e y z : V} {W : Finset V} {r : ℕ}
    (he : e ∈ pathEnds H x W r)
    (hcover : ∀ v, H.Adj e v → v ∈ W ∨ v = y ∨ v = z) :
    (H.neighborSet e).ncard ≤ (pathEnds H x W r).card + 2 := by
  classical
  let S := (H.neighborFinset e).filter fun v => v ∈ W
  have hS : ∀ v ∈ S, H.Adj e v ∧ v ∈ W := by
    intro v hv
    exact ⟨(H.mem_neighborFinset e v).mp (Finset.mem_filter.mp hv).1,
      (Finset.mem_filter.mp hv).2⟩
  have hSbound := endpoint_neighbor_card_le he hS
  have hsub : H.neighborFinset e ⊆ S ∪ {y, z} := by
    intro v hv
    rcases hcover v ((H.mem_neighborFinset e v).mp hv) with hvW | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv, hvW⟩)
    · simp
    · simp
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le S {y, z})
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  have hdegree : (H.neighborFinset e).card ≤ (pathEnds H x W r).card + 2 := by omega
  simpa only [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.ncard_neighborSet] using hdegree

end CycleClique.Construction

end OAI
