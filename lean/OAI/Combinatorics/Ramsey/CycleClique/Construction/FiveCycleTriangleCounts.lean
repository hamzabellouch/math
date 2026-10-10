import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleTriangleOverlap

namespace OAI

/-! The numerical bounds for the four exterior classes at an overlapping triangle. -/

namespace CycleClique.Construction
theorem exterior_clique_card_le_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q A : Finset V} {q : V} (hq : q ∈ Q)
    (hA : A ⊆ exteriorNeighbors G Q q) (hclique : G.IsClique (A : Set V))
    (hω : G.cliqueNum ≤ 3) : A.card ≤ 2 := by
  classical
  have hqA : q ∉ A := by intro h; exact (mem_exteriorNeighbors.mp (hA h)).2 hq
  have hjoin : G.IsClique ((insert q A : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    exact hclique.insert (fun a ha _ => (mem_exteriorNeighbors.mp (hA ha)).1)
  have h := hjoin.card_le_cliqueNum.trans hω
  rw [Finset.card_insert_of_notMem hqA] at h
  omega

theorem four_exterior_sum_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q I A B D : Finset V}
    (hIA : Disjoint (exteriorClosedNeighborhood G Q I) (exteriorClosedNeighborhood G Q A))
    (hIB : Disjoint (exteriorClosedNeighborhood G Q I) (exteriorClosedNeighborhood G Q B))
    (hID : Disjoint (exteriorClosedNeighborhood G Q I) (exteriorClosedNeighborhood G Q D))
    (hAB : Disjoint (exteriorClosedNeighborhood G Q A) (exteriorClosedNeighborhood G Q B))
    (hAD : Disjoint (exteriorClosedNeighborhood G Q A) (exteriorClosedNeighborhood G Q D))
    (hBD : Disjoint (exteriorClosedNeighborhood G Q B) (exteriorClosedNeighborhood G Q D)) :
    Q.card + ((exteriorClosedNeighborhood G Q I).card + (exteriorClosedNeighborhood G Q A).card +
      (exteriorClosedNeighborhood G Q B).card + (exteriorClosedNeighborhood G Q D).card) ≤ Fintype.card V := by
  classical
  let F : Fin 4 → Finset V := ![I, A, B, D]
  have hdis : ∀ i j : Fin 4, i ≠ j → Disjoint (exteriorClosedNeighborhood G Q (F i))
      (exteriorClosedNeighborhood G Q (F j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [F, disjoint_comm]
  have h := exterior_disjoint_sum_bound Finset.univ F (fun i _ j _ hij => hdis i j hij)
  simpa [F, Fin.sum_univ_succ, Nat.add_assoc] using h

theorem overlapping_triangle_card_arithmetic {r a b cI cA cB cD : ℕ}
    (hr : 1 ≤ r) (hU0 : 2 ≤ r + a) (hU1 : 2 ≤ r + b)
    (hI : 4 * r + 1 ≤ 2 + cI) (hA : 0 < a → 4 ≤ cA)
    (hB : 0 < b → 4 ≤ cB) (hD : 4 ≤ cD) (hsum : cI + cA + cB + cD ≤ 14) :
    r = 2 ∧ a = 0 ∧ b = 0 := by
  have hr2 : r ≤ 2 := by omega
  have hrnot1 : r ≠ 1 := by
    intro heq
    have hA' := hA (by omega)
    have hB' := hB (by omega)
    omega
  have hre : r = 2 := by omega
  have ha0 : a = 0 := by
    by_contra hn
    have hA' := hA (by omega)
    omega
  have hb0 : b = 0 := by
    by_contra hn
    have hB' := hB (by omega)
    omega
  exact ⟨hre, ha0, hb0⟩

end CycleClique.Construction

end OAI
