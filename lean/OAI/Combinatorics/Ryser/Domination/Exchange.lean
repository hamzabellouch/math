import OAI.Combinatorics.Ryser.Domination.Basic

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

theorem transversal_exchange {G : Graph V} {pool : V → ι}
    {J : Finset ι} {U : Finset V} {x y : V}
    (hU : IsTransversalOn G pool J U) (hy : y ∈ U)
    (hpool : pool x = pool y) (hfree : ∀ z ∈ U, ¬ G.Adj x z) :
    IsTransversalOn G pool J (insert x (U.erase y)) := by
  rcases hU with ⟨hind, hinj, himage⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rcases Finset.mem_insert.mp ha with hax | haErase
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · rw [hax, hbx]
        exact G.irrefl
      · rw [hax]
        exact hfree b (Finset.mem_of_mem_erase hbErase)
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · rw [hbx]
        intro hab
        exact hfree a (Finset.mem_of_mem_erase haErase) hab.symm
      · exact hind a (Finset.mem_of_mem_erase haErase)
          b (Finset.mem_of_mem_erase hbErase)
  · intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with hax | haErase
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · exact hax.trans hbx.symm
      · have hby : b = y :=
          hinj (Finset.mem_of_mem_erase hbErase) hy
            (hab.symm.trans ((congrArg pool hax).trans hpool))
        exact False.elim ((Finset.mem_erase.mp hbErase).1 hby)
    · rcases Finset.mem_insert.mp hb with hbx | hbErase
      · have hay : a = y :=
          hinj (Finset.mem_of_mem_erase haErase) hy
            (hab.trans ((congrArg pool hbx).trans hpool))
        exact False.elim ((Finset.mem_erase.mp haErase).1 hay)
      · exact hinj (Finset.mem_of_mem_erase haErase)
          (Finset.mem_of_mem_erase hbErase) hab
  · rw [← himage]
    ext i
    constructor
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨z, hz, hzi⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact Finset.mem_image.mpr ⟨y, hy, hpool.symm.trans hzi⟩
      · exact Finset.mem_image.mpr ⟨z, Finset.mem_of_mem_erase hz, hzi⟩
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨z, hz, hzi⟩
      by_cases hzy : z = y
      · subst z
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_insert_self x _, hpool.trans hzi⟩
      · exact Finset.mem_image.mpr
          ⟨z, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzy, hz⟩), hzi⟩

theorem neighborsIn_exchange (G : Graph V) (a x y : V) (U : Finset V)
    (hax : ¬ G.Adj a x) :
    neighborsIn G a (insert x (U.erase y)) = (neighborsIn G a U).erase y := by
  ext z
  simp only [mem_neighborsIn, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨hz, haz⟩
    rcases hz with rfl | hz
    · exact (hax haz).elim
    · exact ⟨hz.1, hz.2, haz⟩
  · intro hz
    exact ⟨Or.inr ⟨hz.1, hz.2.1⟩, hz.2.2⟩

theorem neighborsIn_exchange_eq_of_not_mem (G : Graph V)
    (a x y : V) (U : Finset V) (hax : ¬ G.Adj a x)
    (hy : y ∉ neighborsIn G a U) :
    neighborsIn G a (insert x (U.erase y)) = neighborsIn G a U := by
  rw [neighborsIn_exchange G a x y U hax, Finset.erase_eq_of_notMem hy]

theorem card_neighborsIn_exchange_lt (G : Graph V)
    (a x y : V) (U : Finset V) (hax : ¬ G.Adj a x)
    (hy : y ∈ neighborsIn G a U) :
    (neighborsIn G a (insert x (U.erase y))).card < (neighborsIn G a U).card := by
  rw [neighborsIn_exchange G a x y U hax]
  exact Finset.card_erase_lt_of_mem hy

end RyserCoveringCounterexample.Selection

end OAI
