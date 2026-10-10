import OAI.Combinatorics.Ramsey.CycleClique.Construction.SmallIndependent
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FourCycleCounts

namespace OAI

/-! A residual vertex sees all of at least two triangle exterior classes. -/

namespace CycleClique.Construction
theorem fourCycle_residual_sees_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 3)
    (hcycle : ¬ HasCycle G 4) (hbound : IndependenceBound G 3)
    (q : Fin 3 → V) (hq : Function.Injective q) (hqQ : ∀ i, q i ∈ Q)
    {w : V} (hwQ : w ∉ Q) (hw : ∀ x ∈ Q, ¬ G.Adj w x) :
    ∃ i j : Fin 3, i ≠ j ∧
      (∀ u ∈ exteriorNeighbors G Q (q i), G.Adj w u) ∧
      (∀ v ∈ exteriorNeighbors G Q (q j), G.Adj w v) := by
  classical
  let Full := fun i : Fin 3 => ∀ u ∈ exteriorNeighbors G Q (q i), G.Adj w u
  have hpair : ∀ i j : Fin 3, i ≠ j → Full i ∨ Full j := by
    intro i j hij
    by_contra hn
    simp only [not_or] at hn
    obtain ⟨u, hnu⟩ := not_forall.mp hn.1
    obtain ⟨hu, hwu⟩ := not_imp.mp hnu
    obtain ⟨v, hnv⟩ := not_forall.mp hn.2
    obtain ⟨hv, hwv⟩ := not_imp.mp hnv
    obtain ⟨h, hhi, hhj⟩ := exists_third_fin_three hij
    have hdis := fourCycle_triangle_exterior_disjoint hQ hQcard hcycle (hqQ i) (hqQ j)
      (fun he => hij (hq he))
    have huv : u ≠ v := fun he => Finset.disjoint_left.mp hdis hu (he ▸ hv)
    have huQ := (mem_exteriorNeighbors.mp hu).2
    have hvQ := (mem_exteriorNeighbors.mp hv).2
    have hwu' : w ≠ u := by
      intro he
      exact hw (q i) (hqQ i) (by rw [he]; exact (mem_exteriorNeighbors.mp hu).1.symm)
    have hwv' : w ≠ v := by
      intro he
      exact hw (q j) (hqQ j) (by rw [he]; exact (mem_exteriorNeighbors.mp hv).1.symm)
    have huqh : ¬ G.Adj u (q h) := by
      intro hadj
      have hother : u ∈ exteriorNeighbors G Q (q h) := mem_exteriorNeighbors.mpr ⟨hadj.symm, huQ⟩
      exact Finset.disjoint_left.mp
        (fourCycle_triangle_exterior_disjoint hQ hQcard hcycle (hqQ i) (hqQ h)
          (fun he => hhi (hq he).symm)) hu hother
    have hvqh : ¬ G.Adj v (q h) := by
      intro hadj
      have hother : v ∈ exteriorNeighbors G Q (q h) := mem_exteriorNeighbors.mpr ⟨hadj.symm, hvQ⟩
      exact Finset.disjoint_left.mp
        (fourCycle_triangle_exterior_disjoint hQ hQcard hcycle (hqQ j) (hqQ h)
          (fun he => hhj (hq he).symm)) hv hother
    have hnd : ([w, u, v, q h] : List V).Nodup := by
      simp [hwu', hwv', ne_of_mem_of_not_mem (hqQ h) hwQ |>.symm, huv,
        ne_of_mem_of_not_mem (hqQ h) huQ |>.symm, ne_of_mem_of_not_mem (hqQ h) hvQ |>.symm]
    have hfour := independent_four_card_bound hbound hnd hwu hwv (hw _ (hqQ h))
      (fourCycle_triangle_exterior_anticomplete hQ hcycle (hqQ i) (hqQ j)
        (fun he => hij (hq he)) hu hv) huqh hvqh
    omega
  have h01 := hpair 0 1 (by decide)
  have h02 := hpair 0 2 (by decide)
  have h12 := hpair 1 2 (by decide)
  by_cases h0 : Full 0
  · by_cases h1 : Full 1
    · exact ⟨0, 1, by decide, h0, h1⟩
    · exact ⟨0, 2, by decide, h0, h12.resolve_left h1⟩
  · exact ⟨1, 2, by decide, h01.resolve_left h0, h02.resolve_left h0⟩

end CycleClique.Construction

end OAI
