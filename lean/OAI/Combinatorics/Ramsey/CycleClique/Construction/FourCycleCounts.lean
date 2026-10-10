import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallPacking

namespace OAI

/-! The common-neighbour obstruction to a four-cycle gives sharp small pigeonhole bounds. -/

namespace CycleClique.Construction
theorem fourCycle_common_neighbors_unique {V : Type*} {G : SimpleGraph V}
    (hcycle : ¬ HasCycle G 4) {x y u v : V} (hxy : x ≠ y)
    (hxu : G.Adj x u) (hyu : G.Adj y u) (hxv : G.Adj x v) (hyv : G.Adj y v) : u = v := by
  by_contra huv
  exact hcycle (hasCycle_four_of_edges hxu hyu.symm hyv hxv.symm hxy huv)

theorem fourCycle_common_neighbors_card {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hcycle : ¬ HasCycle G 4) {x y : V} (hxy : x ≠ y) (W : Finset V)
    (hW : ∀ w ∈ W, G.Adj x w ∧ G.Adj y w) : W.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  exact fourCycle_common_neighbors_unique hcycle hxy (hW u hu).1 (hW u hu).2
    (hW v hv).1 (hW v hv).2

theorem fourCycle_three_representatives_bound {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hcycle : ¬ HasCycle G 4) (f : Fin 3 → V)
    (hf : Function.Injective f) (W : Finset V)
    (hW : ∀ w ∈ W, ∃ i j : Fin 3, i ≠ j ∧ G.Adj w (f i) ∧ G.Adj w (f j)) :
    W.card ≤ 3 := by
  classical
  let A := (Finset.univ : Finset (Fin 3)).powersetCard 2
  have hAcard : A.card = 3 := by decide
  have hex : ∀ w : W, ∃ P : A, ∀ i ∈ P.val, G.Adj w.val (f i) := by
    intro w
    obtain ⟨i, j, hij, hwi, hwj⟩ := hW w.val w.property
    refine ⟨⟨{i, j}, ?_⟩, ?_⟩
    · simp only [A, Finset.mem_powersetCard, Finset.subset_univ, Finset.card_pair hij, and_self]
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hwi
      · exact hwj
  let pair : W → A := fun w => Classical.choose (hex w)
  have hpair : ∀ w : W, ∀ i ∈ (pair w).val, G.Adj w.val (f i) :=
    fun w => Classical.choose_spec (hex w)
  have hinj : Function.Injective pair := by
    intro u v huv
    have hcard := (Finset.mem_powersetCard.mp (pair u).property).2
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (pair u).val.card)
    apply Subtype.ext
    exact fourCycle_common_neighbors_unique hcycle (fun h => hij (hf h))
      (hpair u i hi).symm (hpair u j hj).symm
      (hpair v i (by simpa only [huv] using hi)).symm
      (hpair v j (by simpa only [huv] using hj)).symm
  have hc := Fintype.card_le_of_injective pair hinj
  simpa only [Fintype.card_coe, hAcard] using hc

end CycleClique.Construction

end OAI
