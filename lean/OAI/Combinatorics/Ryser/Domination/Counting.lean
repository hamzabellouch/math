import OAI.Combinatorics.Ryser.Domination.TraceDefinitions

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι} {root : ι} {k : ℕ}

theorem verticesY_subset_of_realized (t : DominationTrace G pool J root k)
    {U : Finset V}
    (hreal : ∀ a, a < k → neighborsIn G (t.x a) U = t.y a) :
    t.verticesY ⊆ U := by
  intro v hv
  obtain ⟨a, ha, hva⟩ := mem_verticesY.mp hv
  have hvn : v ∈ neighborsIn G (t.x a) U := by
    rw [hreal a ha]
    exact hva
  exact neighborsIn_subset G (t.x a) U hvn

theorem pool_injOn_verticesY (t : DominationTrace G pool J root k) :
    Set.InjOn pool (t.verticesY : Set V) := by
  obtain ⟨U, hU, hreal⟩ := t.realized
  intro x hx y hy hxy
  exact hU.2.1 (t.verticesY_subset_of_realized hreal hx)
    (t.verticesY_subset_of_realized hreal hy) hxy

theorem image_verticesY_subset (t : DominationTrace G pool J root k) :
    t.verticesY.image pool ⊆ J := by
  obtain ⟨U, hU, hreal⟩ := t.realized
  intro i hi
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
  rw [← hU.2.2]
  exact Finset.mem_image.mpr ⟨x, t.verticesY_subset_of_realized hreal hx, rfl⟩

theorem length_le_card_verticesY (t : DominationTrace G pool J root k) :
    k ≤ t.verticesY.card := by
  have hdisj :
      ((Finset.range k : Finset ℕ) : Set ℕ).PairwiseDisjoint t.y := by
    intro a ha b hb hab
    exact t.disjoint a (Finset.mem_range.mp ha)
      b (Finset.mem_range.mp hb) hab
  simpa only [verticesY, Finset.card_range] using
    (Finset.card_le_card_biUnion hdisj
      (fun a ha => t.nonempty a (Finset.mem_range.mp ha)))

theorem length_le_card (t : DominationTrace G pool J root k) [Fintype V] :
    k ≤ Fintype.card V :=
  t.length_le_card_verticesY.trans (Finset.card_le_univ t.verticesY)

theorem indices_nonempty (t : DominationTrace G pool J root k) :
    t.indices.Nonempty := by
  exact ⟨root, Finset.mem_insert_self root (t.verticesY.image pool)⟩

theorem mem_indices_iff (t : DominationTrace G pool J root k) {i : ι} :
    i ∈ t.indices ↔
      i = root ∨ ∃ b, b < k ∧ ∃ y ∈ t.y b, i = pool y := by
  unfold indices
  constructor
  · intro hi
    rcases Finset.mem_insert.mp hi with hi | hi
    · exact Or.inl hi
    · obtain ⟨y, hy, hpool⟩ := Finset.mem_image.mp hi
      obtain ⟨b, hb, hyb⟩ := mem_verticesY.mp hy
      exact Or.inr ⟨b, hb, y, hyb, hpool.symm⟩
  · intro hi
    apply Finset.mem_insert.mpr
    rcases hi with hi | ⟨b, hb, y, hy, hpool⟩
    · exact Or.inl hi
    · exact Or.inr (Finset.mem_image.mpr
        ⟨y, mem_verticesY.mpr ⟨b, hb, hy⟩, hpool.symm⟩)

theorem vertices_pool_mem (t : DominationTrace G pool J root k) :
    ∀ x ∈ t.vertices, pool x ∈ t.indices := by
  intro x hx
  change x ∈ t.verticesX ∪ t.verticesY at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨a, ha, rfl⟩ := mem_verticesX.mp hx
    apply (mem_indices_iff t).mpr
    rcases t.origin a ha with hpool | ⟨b, hb, y, hy, hpool⟩
    · exact Or.inl hpool
    · exact Or.inr ⟨b, Nat.lt_trans hb ha, y, hy, hpool⟩
  · change pool x ∈ insert root (t.verticesY.image pool)
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

theorem card_verticesX_le (t : DominationTrace G pool J root k) :
    t.verticesX.card ≤ k := by
  simpa only [verticesX, Finset.card_range] using
    (Finset.card_image_le (s := Finset.range k) (f := t.x))

theorem card_indices (t : DominationTrace G pool J root k) (hroot : root ∉ J) :
    t.indices.card = t.verticesY.card + 1 := by
  have hnot : root ∉ t.verticesY.image pool := by
    intro hmem
    exact hroot (t.image_verticesY_subset hmem)
  rw [indices, Finset.card_insert_of_notMem hnot,
    Finset.card_image_of_injOn t.pool_injOn_verticesY]

theorem card_vertices_le (t : DominationTrace G pool J root k)
    (hroot : root ∉ J) :
    t.vertices.card ≤ 2 * (t.indices.card - 1) := by
  calc
    t.vertices.card ≤ t.verticesX.card + t.verticesY.card :=
      Finset.card_union_le t.verticesX t.verticesY
    _ ≤ t.verticesY.card + t.verticesY.card :=
      Nat.add_le_add_right (t.card_verticesX_le.trans t.length_le_card_verticesY) _
    _ = 2 * (t.indices.card - 1) := by
      rw [t.card_indices hroot]
      omega

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
