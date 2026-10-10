import OAI.Geometry.HeilbronnTriangle.Deletion

namespace OAI


namespace Problem355.Alteration

noncomputable def collisionEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β) :
    Finset (Finset ι) := by
  classical
  exact (S.powersetCard 2).filter (fun e =>
    ∃ i ∈ e, ∃ j ∈ e, i ≠ j ∧ f i = f j)

noncomputable def badTripleEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    (bad : β → β → β → Prop) : Finset (Finset ι) := by
  classical
  exact (S.powersetCard 3).filter (fun e =>
    ∃ i ∈ e, ∃ j ∈ e, ∃ k ∈ e,
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ bad (f i) (f j) (f k))

theorem pair_mem_collisionEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    {i j : ι} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) (hf : f i = f j) :
    {i, j} ∈ collisionEdges S f := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hij⟩, ?_⟩
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj
  · exact ⟨i, by simp, j, by simp, hij, hf⟩

theorem triple_mem_badTripleEdges {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    (bad : β → β → β → Prop) {i j k : ι}
    (hi : i ∈ S) (hj : j ∈ S) (hk : k ∈ S)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hbad : bad (f i) (f j) (f k)) :
    {i, j, k} ∈ badTripleEdges S f bad := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_,
    Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩⟩, ?_⟩
  · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi (And.intro hj hk)
  · exact ⟨i, by simp, j, by simp, k, by simp, hij, hik, hjk, hbad⟩

theorem collisionEdges_card_le {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β) :
    (collisionEdges S f).card ≤ Nat.choose S.card 2 := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard 2 S)

theorem badTripleEdges_card_le {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    (bad : β → β → β → Prop) :
    (badTripleEdges S f bad).card ≤ Nat.choose S.card 3 := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_powersetCard 3 S)

theorem exists_sample_subset_avoiding {ι β : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → β)
    (bad : β → β → β → Prop) (n : ℕ)
    (hbudget : n + (collisionEdges S f).card + (badTripleEdges S f bad).card ≤ S.card) :
    ∃ T : Finset ι, T ⊆ S ∧ T.card = n ∧ Set.InjOn f (T : Set ι) ∧
      ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
        i ≠ j → i ≠ k → j ≠ k → ¬ bad (f i) (f j) (f k) := by
  classical
  let F := collisionEdges S f ∪ badTripleEdges S f bad
  have hne : ∀ e ∈ F, e.Nonempty := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · have hc : e.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
      exact Finset.card_pos.mp (by omega)
    · have hc : e.card = 3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
      exact Finset.card_pos.mp (by omega)
  have hFcard : F.card ≤ (collisionEdges S f).card + (badTripleEdges S f bad).card :=
    Finset.card_union_le _ _
  obtain ⟨T, hTS, hcard, havoid⟩ :=
    exists_subset_card_eq_avoiding S F hne n (by omega)
  refine ⟨T, hTS, hcard, ?_, ?_⟩
  · intro i hi j hj hf
    change i ∈ T at hi
    change j ∈ T at hj
    by_contra hij
    have he : {i, j} ∈ F := Finset.mem_union_left _
      (pair_mem_collisionEdges S f (hTS hi) (hTS hj) hij hf)
    exact havoid _ he (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj)
  · intro i hi j hj k hk hij hik hjk hbad
    have he : {i, j, k} ∈ F := Finset.mem_union_right _
      (triple_mem_badTripleEdges S f bad (hTS hi) (hTS hj) (hTS hk) hij hik hjk hbad)
    exact havoid _ he (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi (And.intro hj hk))

end Problem355.Alteration

end OAI
