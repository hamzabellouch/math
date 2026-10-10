import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallPacking

namespace OAI

/-! Small independent sets used in the four- and five-cycle cases. -/

namespace CycleClique.Construction
theorem independent_four_card_bound {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a : ℕ} (hbound : IndependenceBound G a) {w x y z : V}
    (hnd : ([w, x, y, z] : List V).Nodup)
    (hwx : ¬ G.Adj w x) (hwy : ¬ G.Adj w y) (hwz : ¬ G.Adj w z)
    (hxy : ¬ G.Adj x y) (hxz : ¬ G.Adj x z) (hyz : ¬ G.Adj y z) : 4 ≤ a := by
  let I := ([w, x, y, z] : List V).toFinset
  have hreverse : ¬ G.Adj x w ∧ ¬ G.Adj y w ∧ ¬ G.Adj z w ∧
      ¬ G.Adj y x ∧ ¬ G.Adj z x ∧ ¬ G.Adj z y :=
    ⟨fun h => hwx h.symm, fun h => hwy h.symm, fun h => hwz h.symm,
      fun h => hxy h.symm, fun h => hxz h.symm, fun h => hyz h.symm⟩
  have hI : G.IsIndepSet (I : Set V) := by
    intro u hu v hv _ hadj
    simp only [I, Finset.mem_coe, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;> aesop
  have hcard : I.card = 4 := by simpa only [I, List.length_cons, List.length_nil] using List.toFinset_card_of_nodup hnd
  simpa only [hcard] using hbound I hI

theorem exists_third_fin_three {i j : Fin 3} (hij : i ≠ j) :
    ∃ h : Fin 3, h ≠ i ∧ h ≠ j := by
  classical
  have hcard : ({i, j} : Finset (Fin 3)).card < (Finset.univ : Finset (Fin 3)).card := by
    simp only [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨h, _, hh⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  exact ⟨h, by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hh⟩

end CycleClique.Construction

end OAI
