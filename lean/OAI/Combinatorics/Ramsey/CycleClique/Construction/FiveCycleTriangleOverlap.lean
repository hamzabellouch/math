import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleFourClique

namespace OAI

/-! Only one exterior pair can overlap at a triangle in the five-cycle case. -/

namespace CycleClique.Construction
theorem fiveCycle_overlap_misses_third {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 3)
    (hω : G.cliqueNum ≤ 3) (q : Fin 3 → V) (hqcover : ∀ x ∈ Q, ∃ i, q i = x)
    {u : V} (hu : u ∈ exteriorNeighbors G Q (q 0)) (hu' : u ∈ exteriorNeighbors G Q (q 1)) :
    ¬ G.Adj u (q 2) := by
  classical
  intro hu2
  have huQ := (mem_exteriorNeighbors.mp hu).2
  have hjoin : G.IsClique ((insert u Q : Finset V) : Set V) := by
    rw [Finset.coe_insert]
    apply hQ.insert
    intro x hx _
    obtain ⟨i, rfl⟩ := hqcover x hx
    fin_cases i
    · exact (mem_exteriorNeighbors.mp hu).1.symm
    · exact (mem_exteriorNeighbors.mp hu').1.symm
    · exact hu2
  have hc := hjoin.card_le_cliqueNum.trans hω
  rw [Finset.card_insert_of_notMem huQ, hQcard] at hc
  omega

theorem fiveCycle_other_triangle_overlap_absent {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G 5) (q : Fin 3 → V) (hq : Function.Injective q)
    (hqQ : ∀ i, q i ∈ Q)
    {x : V} (hx0 : x ∈ exteriorNeighbors G Q (q 0)) (hx1 : x ∈ exteriorNeighbors G Q (q 1))
    (hx2 : ¬ G.Adj x (q 2)) :
    Disjoint (exteriorNeighbors G Q (q 0)) (exteriorNeighbors G Q (q 2)) ∧
      Disjoint (exteriorNeighbors G Q (q 1)) (exteriorNeighbors G Q (q 2)) := by
  classical
  have hq01 : q 0 ≠ q 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hq h)
  have hq02 : q 0 ≠ q 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hq h)
  have hq12 : q 1 ≠ q 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hq h)
  have hxQ := (mem_exteriorNeighbors.mp hx0).2
  constructor
  · apply Finset.disjoint_left.mpr
    intro y hy0 hy2
    obtain ⟨h0y, hyQ⟩ := mem_exteriorNeighbors.mp hy0
    have h2y := (mem_exteriorNeighbors.mp hy2).1
    have hxy : x ≠ y := fun h => hx2 (by rw [h]; exact h2y.symm)
    have hnd : ([q 1, x, q 0, y, q 2] : List V).Nodup := by
      simp [ne_of_mem_of_not_mem (hqQ 1) hxQ, hq01.symm,
        ne_of_mem_of_not_mem (hqQ 1) hyQ, hq12,
        ne_of_mem_of_not_mem (hqQ 0) hxQ |>.symm, hxy,
        ne_of_mem_of_not_mem (hqQ 2) hxQ |>.symm,
        ne_of_mem_of_not_mem (hqQ 0) hyQ, hq02, h2y.ne.symm]
    exact hcycle (hasCycle_five_of_edges hnd (mem_exteriorNeighbors.mp hx1).1
      (mem_exteriorNeighbors.mp hx0).1.symm h0y h2y.symm (hQ (hqQ 2) (hqQ 1) hq12.symm))
  · apply Finset.disjoint_left.mpr
    intro y hy1 hy2
    obtain ⟨h1y, hyQ⟩ := mem_exteriorNeighbors.mp hy1
    have h2y := (mem_exteriorNeighbors.mp hy2).1
    have hxy : x ≠ y := fun h => hx2 (by rw [h]; exact h2y.symm)
    have hnd : ([q 0, x, q 1, y, q 2] : List V).Nodup := by
      simp [ne_of_mem_of_not_mem (hqQ 0) hxQ, hq01,
        ne_of_mem_of_not_mem (hqQ 0) hyQ, hq02,
        ne_of_mem_of_not_mem (hqQ 1) hxQ |>.symm, hxy,
        ne_of_mem_of_not_mem (hqQ 2) hxQ |>.symm,
        ne_of_mem_of_not_mem (hqQ 1) hyQ, hq12, h2y.ne.symm]
    exact hcycle (hasCycle_five_of_edges hnd (mem_exteriorNeighbors.mp hx0).1
      (mem_exteriorNeighbors.mp hx1).1.symm h1y h2y.symm (hQ (hqQ 2) (hqQ 0) hq02.symm))

theorem fiveCycle_triangle_overlap_independent {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V))
    (hcycle : ¬ HasCycle G 5) (q : Fin 3 → V) (hq : Function.Injective q) (hqQ : ∀ i, q i ∈ Q) :
    G.IsIndepSet ((exteriorNeighbors G Q (q 0) ∩ exteriorNeighbors G Q (q 1) : Finset V) : Set V) := by
  intro x hx y hy hxy hadj
  obtain ⟨hx0, hx1⟩ := Finset.mem_inter.mp hx
  obtain ⟨hy0, hy1⟩ := Finset.mem_inter.mp hy
  have hxQ := (mem_exteriorNeighbors.mp hx0).2
  have hyQ := (mem_exteriorNeighbors.mp hy0).2
  have hq01 : q 0 ≠ q 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hq h)
  have hq02 : q 0 ≠ q 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hq h)
  have hq12 : q 1 ≠ q 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hq h)
  have hnd : ([q 2, q 0, x, y, q 1] : List V).Nodup := by
    simp [hq02.symm, ne_of_mem_of_not_mem (hqQ 2) hxQ,
      ne_of_mem_of_not_mem (hqQ 2) hyQ, hq12.symm,
      ne_of_mem_of_not_mem (hqQ 0) hxQ, ne_of_mem_of_not_mem (hqQ 0) hyQ,
      hq01, hxy, ne_of_mem_of_not_mem (hqQ 1) hxQ |>.symm,
      ne_of_mem_of_not_mem (hqQ 1) hyQ |>.symm]
  exact hcycle (hasCycle_five_of_edges hnd (hQ (hqQ 2) (hqQ 0) hq02.symm)
    (mem_exteriorNeighbors.mp hx0).1 hadj (mem_exteriorNeighbors.mp hy1).1.symm
    (hQ (hqQ 1) (hqQ 2) hq12))

end CycleClique.Construction

end OAI
