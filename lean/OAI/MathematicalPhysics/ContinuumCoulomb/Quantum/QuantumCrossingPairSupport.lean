import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortGraphPairs

namespace OAI

/-! At a selected crossing, every internal port edge is one of its two opposite
pairs. This excludes leftover crossed interactions after edge selection. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMAPortRouteData
variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)

theorem cell_visits_third {p : ℕ × ℕ} {i j k : P.Interior} (hij : i ≠ j)
    (hi : P.cell i = p) (hj : P.cell j = p) (hk : P.cell k = p) : k = i ∨ k = j := by
  by_contra hn
  push Not at hn
  let a : P.CellVisits p := ⟨i,hi⟩
  let b : P.CellVisits p := ⟨j,hj⟩
  let c : P.CellVisits p := ⟨k,hk⟩
  have hab : a ≠ b := fun h => hij (congrArg Subtype.val h)
  have hca : c ≠ a := fun h => hn.1 (congrArg Subtype.val h)
  have hcb : c ≠ b := fun h => hn.2 (congrArg Subtype.val h)
  have hs : ({a,b,c} : Finset (P.CellVisits p)).card = 3 := by simp [hab,hca.symm,hcb.symm]
  have hc := Finset.card_le_univ ({a,b,c} : Finset (P.CellVisits p))
  have hp := P.cellVisits_card p
  omega

theorem crossing_graph_pair {p : ℕ × ℕ} (hp : P.IsCrossing p) {a b : Fin 4}
    (h : P.graph.Adj (qmaGridPort p a) (qmaGridPort p b)) : s(a,b) ∈ qmaCrossPortPairing := by
  obtain ⟨i,j,hij,hi,hj,hpair⟩ := hp
  obtain ⟨k,hk,hab⟩ := P.graph_inner_pair h
  have hki := P.cell_visits_third hij hi hj hk
  rw [← hpair]
  change s(a,b) ∈ {s(P.port i 0,P.port i 1),s(P.port j 0,P.port j 1)}
  rcases hki with rfl | rfl
  · rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert.mpr
      exact Or.inl Sym2.eq_swap
  · rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton.mpr Sym2.eq_swap

end QMAPortRouteData
end ContinuumCoulomb

end

end OAI
