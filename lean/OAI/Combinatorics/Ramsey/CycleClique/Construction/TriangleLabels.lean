import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleNoOverlap

namespace OAI

/-! Labelling a triangle with any prescribed distinct first two vertices. -/

namespace CycleClique.Construction
theorem triangle_label_with_pair {V : Type*} [DecidableEq V] {Q : Finset V}
    (hQcard : Q.card = 3) {x y : V} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y) :
    ∃ q : Fin 3 → V, Function.Injective q ∧ (∀ i, q i ∈ Q) ∧
      (∀ z ∈ Q, ∃ i, q i = z) ∧ q 0 = x ∧ q 1 = y := by
  classical
  obtain ⟨z, hzQ, hznot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({x, y} : Finset V).card < Q.card by rw [Finset.card_pair hxy, hQcard]; omega)
  have hz : z ≠ x ∧ z ≠ y := by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hznot
  let T : Finset V := {x, y, z}
  have hTQ : T ⊆ Q := by simp only [T, Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hx, hy, hzQ⟩
  have hTcard : T.card = 3 := by simp [T, hxy, hz.1.symm, hz.2.symm]
  have hT : T = Q := Finset.eq_of_subset_of_card_le hTQ (by omega)
  let q : Fin 3 → V := ![x, y, z]
  refine ⟨q, ?_, ?_, ?_, rfl, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [q]
  · intro i
    rw [← hT]
    fin_cases i <;> simp [q, T]
  · intro w hw
    rw [← hT] at hw
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem fiveCycle_triangle_exterior_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 3)
    (hcycle : ¬ HasCycle G 5) (hω : G.cliqueNum ≤ 3) (horder : Fintype.card V ≤ 17)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      4 * I.card + 1 ≤ (closedNeighborhood G I).card)
    {x y : V} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x ≠ y) :
    Disjoint (exteriorNeighbors G Q x) (exteriorNeighbors G Q y) := by
  obtain ⟨q, hq, hqQ, hqcover, hq0, hq1⟩ := triangle_label_with_pair hQcard hx hy hxy
  have h := fiveCycle_labelled_triangle_no_overlap hQ hQcard hcycle hω horder hexpand q hq hqQ hqcover
  simpa only [hq0, hq1] using h

end CycleClique.Construction

end OAI
