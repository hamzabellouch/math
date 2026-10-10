import OAI.Combinatorics.Ramsey.CycleClique.Construction.LongestPaths

namespace OAI

/-! Maximum fixed-start paths restricted to a specified induced vertex set. -/

namespace CycleClique.Construction
theorem exists_longest_path_in {V : Type*} [Fintype V]
    (H : SimpleGraph V) (U : Finset V) {x : V} (hx : x ∈ U) :
    ∃ r, ∃ f : Fin (r + 1) → V, IsIndexedPath H f ∧ f 0 = x ∧
      (∀ i, f i ∈ U) ∧
      ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
        (∀ i, g i ∈ U) → q ≤ r := by
  classical
  let K := H.induce (U : Set V)
  let x' : (U : Set V) := ⟨x, hx⟩
  obtain ⟨r, f, hf, hstart, hmax⟩ := exists_longest_path_from K x'
  refine ⟨r, fun i => (f i).val, ⟨Subtype.val_injective.comp hf.1, hf.2⟩,
    congrArg Subtype.val hstart, fun i => (f i).property, ?_⟩
  intro q g hg hgs hgU
  let g' : Fin (q + 1) → (U : Set V) := fun i => ⟨g i, hgU i⟩
  have hg' : IsIndexedPath K g' :=
    ⟨fun a b h => hg.1 (congrArg Subtype.val h), hg.2⟩
  exact hmax q g' hg' (Subtype.ext hgs)

theorem restricted_endpoint_neighbors {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U W : Finset V} {x e : V} {r : ℕ}
    (hWU : W ⊆ U)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r)
    (he : e ∈ pathEnds H x W r) :
    ∀ v ∈ U, H.Adj e v → v ∈ W := by
  intro v hvU hev
  obtain ⟨f, hf, hlast⟩ := mem_pathEnds.mp he
  by_contra hvW
  have hnotrange : v ∉ Set.range f := by
    rw [hf.2.2.2]
    exact hvW
  have hp := indexedPath_snoc ⟨hf.1, hf.2.1⟩ hnotrange (by simpa [hlast] using hev)
  have hU : ∀ i : Fin (r + 1 + 1), (Fin.snoc f v : Fin (r + 1 + 1) → V) i ∈ U := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hvU
    · rw [Fin.snoc_castSucc]
      apply hWU
      change f j ∈ (W : Set V)
      rw [← hf.2.2.2]
      exact ⟨j, rfl⟩
  have h := hmax (r + 1) (Fin.snoc f v) hp (by simpa using hf.2.2.1) hU
  omega

theorem restricted_endpoint_neighbor_cover {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U W : Finset V} {x y z : V} {r : ℕ}
    (hWU : W ⊆ U)
    (hcover : ∀ u ∈ U, ∀ v, H.Adj u v → v ∈ U ∨ v = y ∨ v = z)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r) :
    ∀ e ∈ pathEnds H x W r, ∀ v, H.Adj e v → v ∈ W ∨ v = y ∨ v = z := by
  intro e he v hev
  rcases hcover e (hWU (pathEnds_subset H x W r he)) v hev with hvU | hvy | hvz
  · exact Or.inl (restricted_endpoint_neighbors hWU hmax he v hvU hev)
  · exact Or.inr (Or.inl hvy)
  · exact Or.inr (Or.inr hvz)

end CycleClique.Construction

end OAI
