import OAI.Combinatorics.BalancedRyser.Probability.RootChildDependence

namespace OAI

namespace Balanced.RootChildPartition

theorem touchedPositions_singleton (j : Fin 4) :
    touchedPositions {j} = {j, j - 1} := by
  have h : ∀ j : Fin 4, touchedPositions {j} = {j, j - 1} := by decide
  exact h j

theorem dependentOccurrences_eq_pair {b κ : ℕ} (P : Local.EqualityPattern b κ)
    (R : Finset (Fin b)) (child : Fin b) (j : Fin 4)
    (hchildren : Finset.univ \ R = {child})
    (hgen : rootGeneratorIndices P R child = {j}) :
    dependentOccurrences P R = {(child, j), (child, j - 1)} := by
  simp [dependentOccurrences, hchildren, hgen, touchedPositions_singleton]

theorem exists_one_reuse_linked_pair {b : ℕ} (P : Local.EqualityPattern b 1)
    (hb : 3 ≤ b) :
    ∃ R : Finset (Fin b), ∃ root child : Fin b, ∃ r s : Fin 4,
      DisjointRoots P.classSet R ∧
      root ∈ R ∧ child ∉ R ∧ root ≠ child ∧
      Finset.univ \ R = {child} ∧
      rootGeneratorIndices P R child = {s} ∧
      P.classOf root r = P.classOf child s ∧
      dependentOccurrences P R = {(child, s), (child, s - 1)} ∧
      P.classSet child ∩ (Finset.univ.erase child).biUnion P.classSet ⊆
        R.biUnion P.classSet := by
  obtain ⟨R, hroots, hcard, hchildren⟩ :=
    exists_pattern_roots_exact_of_three_le P hb (by omega)
  obtain ⟨child, hchild⟩ := Finset.card_eq_one.mp hcard
  have hcn : child ∉ R := by
    have h : child ∈ Finset.univ \ R := by rw [hchild]; simp
    exact (Finset.mem_sdiff.mp h).2
  obtain ⟨hone, hprivate⟩ := hchildren child hcn
  have hgens : (rootGeneratorIndices P R child).card = 1 := by
    rw [card_rootGeneratorIndices, hone]
  obtain ⟨s, hs⟩ := Finset.card_eq_one.mp hgens
  have hshared : P.classOf child s ∈ R.biUnion P.classSet := by
    have h : s ∈ rootGeneratorIndices P R child := by rw [hs]; simp
    exact (Finset.mem_filter.mp h).2
  obtain ⟨root, hr, hclass⟩ := Finset.mem_biUnion.mp hshared
  obtain ⟨r, _, hrc⟩ := Finset.mem_image.mp hclass
  refine ⟨R, root, child, r, s, hroots, hr, hcn, ?_, hchild, hs, hrc, ?_, hprivate⟩
  · intro h
    exact hcn (h ▸ hr)
  · exact dependentOccurrences_eq_pair P R child s hchild hs

end Balanced.RootChildPartition

end OAI
