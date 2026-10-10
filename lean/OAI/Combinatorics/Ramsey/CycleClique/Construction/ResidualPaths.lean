import OAI.Combinatorics.Ramsey.CycleClique.Construction.CliqueTraversal
import OAI.Combinatorics.Ramsey.CycleClique.Construction.ColouredPathStart
import OAI.Combinatorics.Ramsey.CycleClique.Construction.SingleAttachment

namespace OAI

/-! Joining the endpoint clique to a path in the remaining component. -/

namespace CycleClique.Construction
/-- The pair consisting of the remaining-path endpoint and a vertex
of the endpoint clique directly gives the needed combined order. -/
theorem endpoint_residual_order {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {E R : Finset V} {u v w y z : V} {s : ℕ}
    (hu : u ∈ R) (hv : v ∈ R) (hw : w ∈ E)
    (hcoverv : ∀ a, H.Adj v a → a ∈ R ∨ a = y ∨ a = z)
    (hcoverw : ∀ a, H.Adj w a → a ∈ E ∨ a = u ∨ a = y ∨ a = z)
    (hexpand : 2 * s ≤ (closedNeighborhood H {v, w}).card) :
    2 * s - 2 ≤ E.card + R.card := by
  classical
  have hsub : closedNeighborhood H {v, w} ⊆ (R ∪ E) ∪ {y, z} := by
    intro a ha
    rcases mem_closedNeighborhood.mp ha with ha | ⟨b, hb, hba⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hw)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · rcases hcoverv a hba with ha | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha)
        · simp
        · simp
      · rcases hcoverw a hba with ha | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)
        · simp
        · simp
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le (R ∪ E) {y, z})
  have hRE := Finset.card_union_le R E
  have hp : ({y, z} : Finset V).card ≤ 2 := Finset.card_le_two
  omega

/-- Traverse the whole endpoint clique first, entering the remaining
path through one of two attachment neighbours. -/
theorem clique_join_remaining_path {V : Type*} [DecidableEq V]
    {H : SimpleGraph V} {E : Finset V} {u w : V}
    (hclique : H.IsClique (E : Set V)) (hw : w ∈ E)
    (hattach : ∃ a ∈ E, ∃ b ∈ E, a ≠ b ∧ H.Adj a u ∧ H.Adj b u)
    (R : List V) (hR : R.Nodup) (hRchain : R.IsChain H.Adj)
    (hRhead : R.head? = some u) (hRoutside : ∀ v ∈ R, v ∉ E) :
    ∃ L : List V, L.Nodup ∧ L.IsChain H.Adj ∧ L.head? = some w ∧
      L.length = E.card + R.length ∧ ∀ v ∈ L, v ∈ E ∨ v ∈ R := by
  obtain ⟨a, ha, b, hb, hab, hau, hbu⟩ := hattach
  have hex : ∃ b ∈ E, w ≠ b ∧ H.Adj b u := by
    by_cases hwa : w = a
    · exact ⟨b, hb, hwa ▸ hab, hbu⟩
    · exact ⟨a, ha, hwa, hau⟩
  obtain ⟨b', hb', hwb', hb'u⟩ := hex
  obtain ⟨P, hP, hPchain, hPlen, hPhead, hPlast, hPmem⟩ :=
    exists_clique_traversal hclique hw hb' hwb'
  have hnodup : (P ++ R).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hP, hR, ?_⟩
    intro a ha b hb heq
    subst b
    exact hRoutside a hb (hPmem a ha)
  have hchain : (P ++ R).IsChain H.Adj := by
    apply List.isChain_append.mpr
    refine ⟨hPchain, hRchain, ?_⟩
    intro a ha b hb
    have hae : b' = a := by simpa only [hPlast, Option.mem_some_iff] using ha
    have hbe : u = b := by simpa only [hRhead, Option.mem_some_iff] using hb
    exact hae ▸ hbe ▸ hb'u
  refine ⟨P ++ R, hnodup, hchain, ?_, by simp only [List.length_append, hPlen], ?_⟩
  · simp only [List.head?_append, hPhead, Option.some_or]
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact Or.inl (hPmem v hv)
    · exact Or.inr hv

theorem no_colored_path_list_bound {V : Type*} {H : SimpleGraph V}
    {x y z : V} (hxy : H.Adj x y) (hxz : H.Adj x z)
    (χ : V → Fin 2) (hyz : χ y ≠ χ z) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hno : ¬ ∃ g : Fin (ℓ + 1) → V, IsIndexedPath H g ∧
      χ (g 0) ≠ χ (g (Fin.last ℓ)))
    {L : List V} (hL : L.Nodup) (hchain : L.IsChain H.Adj)
    (hhead : L.head? = some x) (havoid : ∀ v ∈ L, v ≠ y ∧ v ≠ z) :
    L.length < ℓ := by
  cases L with
  | nil => simp only [List.length_nil]; omega
  | cons a L =>
    let f : Fin (L.length + 1) → V := (a :: L).get
    have hf : IsIndexedPath H f := indexedPath_of_list (a :: L) hL hchain rfl
    have hstart : f 0 = x := by simpa [f] using hhead
    have havoid' : ∀ i, f i ≠ y ∧ f i ≠ z := fun i => havoid _ (List.get_mem _ _)
    exact no_colored_path_start_bound hxy hxz χ hyz hℓ hno hf hstart havoid'

end CycleClique.Construction

end OAI
