import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallCycleGeometry

namespace OAI

/-! Maximum independent sets in separated exterior classes can be added. -/

namespace CycleClique.Construction
theorem indepNum_packing {V ι : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a : ℕ} (hbound : IndependenceBound G a)
    (F : Finset ι) (U : ι → Finset V)
    (hdis : (F : Set ι).PairwiseDisjoint U)
    (hanti : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, ¬ G.Adj x y) :
    ∑ i ∈ F, (G.induce (U i : Set V)).indepNum ≤ a := by
  classical
  have h := independent_packing hbound F (fun i => independentOn G (U i))
    (fun i _ => independentOn_independent G (U i)) (by
      intro i hi j hj hij
      exact (hdis hi hj hij).mono (independentOn_subset G (U i)) (independentOn_subset G (U j))) (by
      intro i hi j hj hij x hx y hy
      exact hanti i hi j hj hij x (independentOn_subset G (U i) hx) y (independentOn_subset G (U j) hy))
  simpa only [independentOn_card] using h

theorem separated_three_cliques {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a : ℕ} (hbound : IndependenceBound G a) (ha : a ≤ 3)
    (U : Fin 3 → Finset V) (hne : ∀ i, (U i).Nonempty)
    (hdis : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hanti : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, ¬ G.Adj x y) :
    a = 3 ∧ ∀ i, G.IsClique (U i : Set V) := by
  classical
  have hpack := indepNum_packing hbound Finset.univ U
    (fun i _ j _ hij => hdis i j hij) (fun i _ j _ hij => hanti i j hij)
  have hpos : ∀ i, 1 ≤ (G.induce (U i : Set V)).indepNum := by
    intro i
    let : Nonempty (U i) := (hne i).to_subtype
    exact indepNum_pos_of_nonempty _
  have hsum : (G.induce (U 0 : Set V)).indepNum +
      (G.induce (U 1 : Set V)).indepNum + (G.induce (U 2 : Set V)).indepNum ≤ a := by
    simpa only [Fin.sum_univ_three, Nat.add_assoc] using hpack
  have haeq : a = 3 := by have := hpos 0; have := hpos 1; have := hpos 2; omega
  refine ⟨haeq, ?_⟩
  intro i
  have hi : (G.induce (U i : Set V)).indepNum ≤ 1 := by
    have := hpos 0
    have := hpos 1
    have := hpos 2
    have h₀ : (G.induce (U 0 : Set V)).indepNum ≤ 1 := by omega
    have h₁ : (G.induce (U 1 : Set V)).indepNum ≤ 1 := by omega
    have h₂ : (G.induce (U 2 : Set V)).indepNum ≤ 1 := by omega
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  have hcomplete := complete_of_indepNum_le_one hi
  intro x hx y hy hxy
  have hadj : (G.induce (U i : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
    rw [hcomplete]
    exact fun h => hxy (congrArg Subtype.val h)
  exact hadj

end CycleClique.Construction

end OAI
