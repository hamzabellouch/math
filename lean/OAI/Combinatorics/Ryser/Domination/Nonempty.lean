import OAI.Combinatorics.Ryser.Domination.TraceDefinitions
import OAI.Combinatorics.Ryser.Domination.Exchange
import OAI.Combinatorics.Ryser.Domination.Seed

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι]

namespace DominationTrace

variable {G : Graph V} {pool : V → ι} {J : Finset ι}
    {root : ι} {k : ℕ}

theorem neighbors_nonempty (t : DominationTrace G pool J root k)
    (hroot : root ∉ J)
    (hno : ¬ ∃ U', IsTransversalOn G pool (insert root J) U')
    {v : V} {U : Finset V} (hU : IsTransversalOn G pool J U)
    (hreal : ∀ a, a < k → neighborsIn G (t.x a) U = t.y a)
    (hvpool : pool v ∈ t.indices)
    (hvfree : ∀ z ∈ t.vertices, ¬ G.Adj v z) :
    (neighborsIn G v U).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  have hfreeU := neighborsIn_eq_empty_iff.mp hempty
  have hax (a : ℕ) (ha : a < k) : ¬ G.Adj (t.x a) v := by
    have hmem : t.x a ∈ t.vertices := by
      change t.x a ∈ t.verticesX ∪ t.verticesY
      exact Finset.mem_union_left _ (mem_verticesX.mpr ⟨a, ha, rfl⟩)
    intro hav
    exact hvfree (t.x a) hmem hav.symm
  change pool v ∈ insert root (t.verticesY.image pool) at hvpool
  rcases Finset.mem_insert.mp hvpool with hvroot | hvimage
  · exact hno ⟨insert v U, transversal_insert_new hU hroot hvroot hfreeU⟩
  · obtain ⟨y, hy, hypool⟩ := Finset.mem_image.mp hvimage
    obtain ⟨b, hb, hyb⟩ := mem_verticesY.mp hy
    have hyn : y ∈ neighborsIn G (t.x b) U := by
      rw [hreal b hb]
      exact hyb
    have hyU : y ∈ U := (mem_neighborsIn.mp hyn).1
    have hU' := transversal_exchange hU hyU hypool.symm hfreeU
    have hearlier : ∀ a, a < b →
        neighborsIn G (t.x a) (insert v (U.erase y)) = t.y a := by
      intro a ha
      have hak : a < k := lt_trans ha hb
      have hyold : y ∉ neighborsIn G (t.x a) U := by
        rw [hreal a hak]
        intro hya
        exact Finset.disjoint_left.mp
          (t.disjoint a hak b hb (Nat.ne_of_lt ha)) hya hyb
      exact (neighborsIn_exchange_eq_of_not_mem G (t.x a) v y U
        (hax a hak) hyold).trans (hreal a hak)
    have hmin := t.minimal b hb (insert v (U.erase y)) hU' hearlier
    have hstrict := card_neighborsIn_exchange_lt G (t.x b) v y U (hax b hb) hyn
    rw [hreal b hb] at hstrict
    exact Nat.not_lt_of_ge hmin hstrict

end DominationTrace
end RyserCoveringCounterexample.Selection

end OAI
