import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTranslatedInternalSeparation

namespace OAI

/-! An interior corridor point belongs to the nonterminal part of one of its
two cell-local halves. -/

namespace ContinuumCoulomb

theorem qmaListInterior_ne_head {α : Type*} {l : List α} (hl : l.Nodup)
    {z a : α} (ha : l.head? = some a) (hz : z ∈ (l.drop 1).dropLast) : z ≠ a := by
  obtain ⟨t,rfl⟩ := List.head?_eq_some_iff.mp ha
  have ht : z ∈ t := List.mem_of_mem_dropLast hz
  intro h
  subst z
  exact (List.nodup_cons.mp hl).1 ht

theorem qmaListInterior_ne_last {l : List (ℕ × ℕ)} (hl : l.Nodup)
    {z a : ℕ × ℕ} (ha : l.getLast? = some a) (hz : z ∈ (l.drop 1).dropLast) : z ≠ a := by
  apply qmaListInterior_ne_head (List.nodup_reverse.mpr hl)
  · simpa only [List.head?_reverse] using ha
  · apply List.mem_toFinset.mp
    rw [qmaInterior_reverse]
    exact List.mem_toFinset.mpr hz

theorem qmaList_mem_drop_one {α : Type*} {l : List α} {z a : α}
    (ha : l.head? = some a) (hz : z ∈ l) (hne : z ≠ a) : z ∈ l.drop 1 := by
  obtain ⟨t,rfl⟩ := List.head?_eq_some_iff.mp ha
  rcases List.mem_cons.mp hz with h | h
  · exact (hne h).elim
  · exact h

theorem qmaCellCorridor_interior {p z : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2)
    {a : Fin 4} {b c : Bool} (hz : z ∈ ((qmaCellCorridor p a b c).drop 1).dropLast) :
    z ∈ (qmaHalfPathAt p b a).drop 1 ∨
      z ∈ (qmaHalfPathAt (qmaGridNeighbor p a) c (qmaPortOpposite a)).drop 1 := by
  have hs := qmaCellCorridor_simple p hp a b c
  have hfirst := qmaListInterior_ne_head hs (qmaCellCorridor_endpoints p a b c).1 hz
  have hlast := qmaListInterior_ne_last hs (qmaCellCorridor_endpoints p a b c).2 hz
  have hm := List.mem_of_mem_drop (List.mem_of_mem_dropLast hz)
  rcases List.mem_append.mp hm with h | h
  · exact Or.inl (qmaList_mem_drop_one (qmaHalfPathAt_endpoints p b a).1 h hfirst)
  · exact Or.inr (qmaList_mem_drop_one
      (qmaHalfPathAt_endpoints (qmaGridNeighbor p a) c (qmaPortOpposite a)).1
      (List.mem_reverse.mp h) hlast)

end ContinuumCoulomb

end OAI
