import OAI.MeasureTheory.Falconer.Estimates.ScalarPrefixTruncation

namespace OAI

/-! Pruning nonempty collections of whole children preserves every coarser
 prefix and every finer branch above an occupied retained node. -/
namespace Falconer.Regularization

 theorem prefixChildren_eq_filter (L : Finset (CellPath 1)) {a b : ℕ}
    (hab : a ≤ b) (p : CellPath 1) :
    prefixChildren L a b p = (L.image (List.take b)).filter (fun q => q.take a = p) := by
  classical
  ext c
  constructor
  · intro hc
    exact Finset.mem_filter.mpr ⟨prefixChildren_mem_image hc,
      scalar_prefix_children_parent hab L p c hc⟩
  · intro hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
    have hp := (Finset.mem_filter.mp hc).2
    simp only [List.take_take,min_eq_left hab] at hp
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hq,hp⟩)

 theorem scalarPruneLeaves_lift (L : Finset (CellPath 1)) {a b : ℕ}
    (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p)
    {q : CellPath 1} (hq : q ∈ L) :
    ∃ u ∈ scalarPruneLeaves L a b K, u.take a = q.take a := by
  classical
  obtain ⟨c,hc⟩ := (hK (q.take a) (Finset.mem_image_of_mem _ hq)).1
  obtain ⟨u,hu,huc⟩ := Finset.mem_image.mp
    ((hK (q.take a) (Finset.mem_image_of_mem _ hq)).2 hc)
  have hua := (Finset.mem_filter.mp hu).2
  refine ⟨u,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,?_⟩,hua⟩
  rw [hua,huc]
  exact hc

 theorem scalarPruneLeaves_upper_prefixes (L : Finset (CellPath 1)) {a b c : ℕ}
    (hca : c ≤ a) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p) :
    (scalarPruneLeaves L a b K).image (List.take c) = L.image (List.take c) := by
  classical
  apply Finset.Subset.antisymm
  · exact Finset.image_subset_image (scalarPruneLeaves_subset L a b K)
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨u,hu,hua⟩ := scalarPruneLeaves_lift L K hK hq
    exact Finset.mem_image.mpr ⟨u,hu,take_eq_of_take_eq hca hua⟩

 theorem scalarPruneLeaves_upper_children (L : Finset (CellPath 1)) {a b c d : ℕ}
    (hcd : c ≤ d) (hda : d ≤ a) (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p)
    (p : CellPath 1) :
    prefixChildren (scalarPruneLeaves L a b K) c d p = prefixChildren L c d p := by
  rw [prefixChildren_eq_filter _ hcd,prefixChildren_eq_filter _ hcd,
    scalarPruneLeaves_upper_prefixes L hda K hK]

 theorem scalarPruneLeaves_nonempty (L : Finset (CellPath 1)) (hne : L.Nonempty) {a b : ℕ}
    (K : CellPath 1 → Finset (CellPath 1))
    (hK : ∀ p ∈ L.image (List.take a), (K p).Nonempty ∧ K p ⊆ prefixChildren L a b p) :
    (scalarPruneLeaves L a b K).Nonempty := by
  obtain ⟨q,hq⟩ := hne
  obtain ⟨u,hu,_⟩ := scalarPruneLeaves_lift L K hK hq
  exact ⟨u,hu⟩

 theorem scalar_single_child_choice (L : Finset (CellPath 1)) (a b : ℕ) :
    ∃ K : CellPath 1 → Finset (CellPath 1),
      ∀ p ∈ L.image (List.take a), K p ⊆ prefixChildren L a b p ∧ (K p).card = 1 := by
  classical
  have hne : ∀ p ∈ L.image (List.take a), (prefixChildren L a b p).Nonempty := by
    intro p hp
    exact (prefixFiber_nonempty hp).image _
  let K : CellPath 1 → Finset (CellPath 1) := fun p => if hp : p ∈ L.image (List.take a) then {(hne p hp).choose} else ∅
  refine ⟨K,?_⟩
  intro p hp
  simp only [K,dite_eq_left hp,Finset.singleton_subset_iff,Finset.card_singleton]
  exact ⟨(hne p hp).choose_spec,trivial⟩

 theorem prefixFiber_total_card (L : Finset (CellPath 1)) (a : ℕ) :
    L.card = ∑ p ∈ L.image (List.take a), (prefixFiber L a p).card := by
  have hh := prefixFiber_card_sum (C := L) (Nat.zero_le a) ([] : CellPath 1)
  simpa only [prefixFiber_zero,prefixChildren] using hh

end Falconer.Regularization

end OAI
