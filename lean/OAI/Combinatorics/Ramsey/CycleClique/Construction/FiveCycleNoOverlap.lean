import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleOverlapStructure

namespace OAI

/-! Reapplying the necessary overlap structure to a neighbouring triangle rules out every overlap. -/

namespace CycleClique.Construction
theorem fiveCycle_labelled_triangle_no_overlap {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 3)
    (hcycle : ¬ HasCycle G 5) (hω : G.cliqueNum ≤ 3) (horder : Fintype.card V ≤ 17)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      4 * I.card + 1 ≤ (closedNeighborhood G I).card)
    (q : Fin 3 → V) (hq : Function.Injective q) (hqQ : ∀ i, q i ∈ Q)
    (hqcover : ∀ x ∈ Q, ∃ i, q i = x) :
    Disjoint (exteriorNeighbors G Q (q 0)) (exteriorNeighbors G Q (q 1)) := by
  classical
  by_contra hdis
  have hoverlap : (exteriorNeighbors G Q (q 0) ∩ exteriorNeighbors G Q (q 1)).Nonempty := by
    obtain ⟨w, hw0, hw1⟩ := Finset.not_disjoint_iff.mp hdis
    exact ⟨w, Finset.mem_inter.mpr ⟨hw0, hw1⟩⟩
  obtain ⟨hIcard, hIeq, _, _, _, hIlower⟩ :=
    fiveCycle_overlap_structure hQ hQcard hcycle hω horder hexpand q hq hqQ hqcover hoverlap
  let I := exteriorNeighbors G Q (q 0)
  have hIq1 : ∀ w ∈ I, w ∈ exteriorNeighbors G Q (q 1) := by intro w hw; rwa [← hIeq]
  have hq01 : q 0 ≠ q 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hq h)
  have hq02 : q 0 ≠ q 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hq h)
  have hq12 : q 1 ≠ q 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hq h)
  have hdegree : ∀ w ∈ I, (exteriorNeighbors G Q w).card = 2 := by
    intro w hw
    have hw0 := (mem_exteriorNeighbors.mp hw).1
    have hw1 := (mem_exteriorNeighbors.mp (hIq1 w hw)).1
    have hwQ := (mem_exteriorNeighbors.mp hw).2
    have hw2 := fiveCycle_overlap_misses_third hQ hQcard hω q hqcover hw (hIq1 w hw)
    let T : Finset V := {q 0, q 1, w}
    have hT : G.IsNClique 3 T := SimpleGraph.is3Clique_triple_iff.mpr
      ⟨hQ (hqQ 0) (hqQ 1) hq01, hw0, hw1⟩
    let q' : Fin 3 → V := ![q 0, q 1, w]
    have h0w := hw0.ne
    have h1w := hw1.ne
    have hq' : Function.Injective q' := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [q']
    have hq'T : ∀ i, q' i ∈ T := by intro i; fin_cases i <;> simp [q', T]
    have hq'cover : ∀ x ∈ T, ∃ i, q' i = x := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    have hq2T : q 2 ∉ T := by
      simp only [T, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hq02.symm, hq12.symm, ne_of_mem_of_not_mem (hqQ 2) hwQ⟩
    have hTov : (exteriorNeighbors G T (q' 0) ∩ exteriorNeighbors G T (q' 1)).Nonempty := by
      refine ⟨q 2, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact mem_exteriorNeighbors.mpr ⟨hQ (hqQ 0) (hqQ 2) hq02, hq2T⟩
      · exact mem_exteriorNeighbors.mpr ⟨hQ (hqQ 1) (hqQ 2) hq12, hq2T⟩
    obtain ⟨_, _, _, hTwocard, _, _⟩ := fiveCycle_overlap_structure hT.isClique hT.card_eq
      hcycle hω horder hexpand q' hq' hq'T hq'cover hTov
    have hset : exteriorNeighbors G Q w = exteriorNeighbors G T w := by
      ext v
      rw [mem_exteriorNeighbors, mem_exteriorNeighbors]
      constructor
      · rintro ⟨hwv, hvQ⟩
        refine ⟨hwv, ?_⟩
        intro hvT
        simp only [T, Finset.mem_insert, Finset.mem_singleton] at hvT
        rcases hvT with rfl | rfl | rfl
        · exact hvQ (hqQ 0)
        · exact hvQ (hqQ 1)
        · exact G.irrefl hwv
      · rintro ⟨hwv, hvT⟩
        refine ⟨hwv, ?_⟩
        intro hvQ
        obtain ⟨i, rfl⟩ := hqcover v hvQ
        fin_cases i
        · exact hvT (by simp [T])
        · exact hvT (by simp [T])
        · exact hw2 hwv
    rw [hset]
    exact hTwocard
  have hsub : exteriorClosedNeighborhood G Q I ⊆ I ∪ I.biUnion (fun w => exteriorNeighbors G Q w) := by
    intro v hv
    obtain ⟨hvI, hvQ⟩ := mem_exteriorClosedNeighborhood.mp hv
    rcases hvI with hvI | ⟨w, hw, hwv⟩
    · exact Finset.mem_union_left _ hvI
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw, mem_exteriorNeighbors.mpr ⟨hwv, hvQ⟩⟩)
  have hupper := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (Finset.card_biUnion_le) I.card))
  change I.card = 2 at hIcard
  have hsum : (∑ w ∈ I, (exteriorNeighbors G Q w).card) = 4 := by
    rw [Finset.sum_congr rfl (fun w hw => hdegree w hw)]
    simp only [Finset.sum_const, hIcard, smul_eq_mul]
  change 7 ≤ (exteriorClosedNeighborhood G Q I).card at hIlower
  rw [hsum] at hupper
  omega

end CycleClique.Construction

end OAI
