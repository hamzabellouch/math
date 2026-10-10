import OAI.Combinatorics.Ramsey.CycleClique.Construction.FiveCycleTriangleCounts

namespace OAI

/-! The exact two-vertex overlap forced at every overlapping triangle. -/

namespace CycleClique.Construction
theorem fiveCycle_overlap_structure {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {Q : Finset V} (hQ : G.IsClique (Q : Set V)) (hQcard : Q.card = 3)
    (hcycle : ¬ HasCycle G 5) (hω : G.cliqueNum ≤ 3) (horder : Fintype.card V ≤ 17)
    (hexpand : ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.Nonempty →
      4 * I.card + 1 ≤ (closedNeighborhood G I).card)
    (q : Fin 3 → V) (hq : Function.Injective q) (hqQ : ∀ i, q i ∈ Q)
    (hqcover : ∀ x ∈ Q, ∃ i, q i = x)
    (hoverlap : (exteriorNeighbors G Q (q 0) ∩ exteriorNeighbors G Q (q 1)).Nonempty) :
    (exteriorNeighbors G Q (q 0)).card = 2 ∧
      exteriorNeighbors G Q (q 0) = exteriorNeighbors G Q (q 1) ∧
      G.IsIndepSet (exteriorNeighbors G Q (q 0) : Set V) ∧
      (exteriorNeighbors G Q (q 2)).card = 2 ∧
      G.IsClique (exteriorNeighbors G Q (q 2) : Set V) ∧
      7 ≤ (exteriorClosedNeighborhood G Q (exteriorNeighbors G Q (q 0))).card := by
  classical
  let U := fun i => exteriorNeighbors G Q (q i)
  let I := U 0 ∩ U 1
  let A := U 0 \ I
  let B := U 1 \ I
  let D := U 2
  have hI0 : I ⊆ U 0 := Finset.inter_subset_left
  have hI1 : I ⊆ U 1 := Finset.inter_subset_right
  have hA0 : A ⊆ U 0 := Finset.sdiff_subset
  have hB1 : B ⊆ U 1 := Finset.sdiff_subset
  have hIne : I.Nonempty := hoverlap
  obtain ⟨x, hx⟩ := hoverlap
  obtain ⟨hx0, hx1⟩ := Finset.mem_inter.mp hx
  have hx2 := fiveCycle_overlap_misses_third hQ hQcard hω q hqcover hx0 hx1
  obtain ⟨h02, h12⟩ := fiveCycle_other_triangle_overlap_absent hQ hcycle q hq hqQ hx0 hx1 hx2
  have hq01 : q 0 ≠ q 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hq h)
  have hq02 : q 0 ≠ q 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hq h)
  have hq12 : q 1 ≠ q 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hq h)
  have hlow : ∀ i, 2 ≤ (U i).card := by
    intro i
    have hs := hexpand {q i} (by simp) (by simp)
    simp only [Finset.card_singleton, Nat.mul_one] at hs
    have h := exteriorNeighbors_card_lower (hqQ i) hs
    rw [hQcard] at h
    change 5 ≤ 3 + (U i).card at h
    omega
  have houtside : ∀ i, Disjoint (U i) Q := by
    intro i
    apply Finset.disjoint_left.mpr
    intro u hu huQ
    exact (mem_exteriorNeighbors.mp hu).2 huQ
  have hIQ : Disjoint I Q := (houtside 0).mono_left hI0
  have hAQ : Disjoint A Q := (houtside 0).mono_left hA0
  have hBQ : Disjoint B Q := (houtside 1).mono_left hB1
  have hDQ : Disjoint D Q := houtside 2
  have hIA : Disjoint I A := by
    apply Finset.disjoint_left.mpr
    intro u hu huA
    exact (Finset.mem_sdiff.mp huA).2 hu
  have hIB : Disjoint I B := by
    apply Finset.disjoint_left.mpr
    intro u hu huB
    exact (Finset.mem_sdiff.mp huB).2 hu
  have hID : Disjoint I D := h02.mono_left hI0
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro u huA huB
    exact (Finset.mem_sdiff.mp huA).2 (Finset.mem_inter.mpr ⟨hA0 huA, hB1 huB⟩)
  have hAD : Disjoint A D := h02.mono_left hA0
  have hBD : Disjoint B D := h12.mono_left hB1
  have hCsum := four_exterior_sum_bound
    (fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ 1) (hqQ 0) hq01.symm hI1 hA0 hIA)
    (fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ 0) (hqQ 1) hq01 hI0 hB1 hIB)
    (fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ 0) (hqQ 2) hq02 hI0 (fun _ h => h) hID)
    (fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ 0) (hqQ 1) hq01 hA0 hB1 hAB)
    (fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ 0) (hqQ 2) hq02 hA0 (fun _ h => h) hAD)
    (fiveCycle_exterior_closed_disjoint hQ (by omega) hcycle (hqQ 1) (hqQ 2) hq12 hB1 (fun _ h => h) hBD)
  rw [hQcard] at hCsum
  change 3 + ((exteriorClosedNeighborhood G Q I).card + (exteriorClosedNeighborhood G Q A).card +
    (exteriorClosedNeighborhood G Q B).card + (exteriorClosedNeighborhood G Q D).card) ≤ Fintype.card V at hCsum
  have hsum : (exteriorClosedNeighborhood G Q I).card + (exteriorClosedNeighborhood G Q A).card +
      (exteriorClosedNeighborhood G Q B).card + (exteriorClosedNeighborhood G Q D).card ≤ 14 := by omega
  have hcoverI : ∀ u ∈ I, ∀ z ∈ Q, G.Adj u z → z ∈ ({q 0, q 1} : Finset V) := by
    intro u hu z hz huz
    obtain ⟨i, rfl⟩ := hqcover z hz
    fin_cases i
    · simp
    · simp
    · exact False.elim (fiveCycle_overlap_misses_third hQ hQcard hω q hqcover (hI0 hu) (hI1 hu) huz)
  have hcoverA : ∀ u ∈ A, ∀ z ∈ Q, G.Adj u z → z = q 0 := by
    intro u hu z hz huz
    obtain ⟨i, rfl⟩ := hqcover z hz
    fin_cases i
    · rfl
    · have hu1 : u ∈ U 1 := mem_exteriorNeighbors.mpr ⟨huz.symm, (mem_exteriorNeighbors.mp (hA0 hu)).2⟩
      exact False.elim ((Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mpr ⟨hA0 hu, hu1⟩))
    · have hu2 : u ∈ U 2 := mem_exteriorNeighbors.mpr ⟨huz.symm, (mem_exteriorNeighbors.mp (hA0 hu)).2⟩
      exact False.elim (Finset.disjoint_left.mp h02 (hA0 hu) hu2)
  have hcoverB : ∀ u ∈ B, ∀ z ∈ Q, G.Adj u z → z = q 1 := by
    intro u hu z hz huz
    obtain ⟨i, rfl⟩ := hqcover z hz
    fin_cases i
    · have hu0 : u ∈ U 0 := mem_exteriorNeighbors.mpr ⟨huz.symm, (mem_exteriorNeighbors.mp (hB1 hu)).2⟩
      exact False.elim ((Finset.mem_sdiff.mp hu).2 (Finset.mem_inter.mpr ⟨hu0, hB1 hu⟩))
    · rfl
    · have hu2 : u ∈ U 2 := mem_exteriorNeighbors.mpr ⟨huz.symm, (mem_exteriorNeighbors.mp (hB1 hu)).2⟩
      exact False.elim (Finset.disjoint_left.mp h12 (hB1 hu) hu2)
  have hcoverD : ∀ u ∈ D, ∀ z ∈ Q, G.Adj u z → z = q 2 := by
    intro u hu z hz huz
    obtain ⟨i, rfl⟩ := hqcover z hz
    fin_cases i
    · have hu0 : u ∈ U 0 := mem_exteriorNeighbors.mpr ⟨huz.symm, (mem_exteriorNeighbors.mp hu).2⟩
      exact False.elim (Finset.disjoint_left.mp h02 hu0 hu)
    · have hu1 : u ∈ U 1 := mem_exteriorNeighbors.mpr ⟨huz.symm, (mem_exteriorNeighbors.mp hu).2⟩
      exact False.elim (Finset.disjoint_left.mp h12 hu1 hu)
    · rfl
  have hIind : G.IsIndepSet (I : Set V) := fiveCycle_triangle_overlap_independent hQ hcycle q hq hqQ
  have hIgrow : 4 * I.card + 1 ≤ 2 + (exteriorClosedNeighborhood G Q I).card := by
    have h := exterior_closed_expansion_bound (hexpand I hIind hIne) (Finset.Subset.refl I) hIQ hcoverI
    simpa only [Finset.card_pair hq01] using h
  have hAgrow : 0 < A.card → 4 ≤ (exteriorClosedNeighborhood G Q A).card := by
    intro ha
    let : Nonempty A := (Finset.card_pos.mp ha).to_subtype
    have hpos := indepNum_pos_of_nonempty (G.induce (A : Set V))
    have hg := one_clique_neighbor_expansion (Finset.card_pos.mp ha) hAQ hcoverA hexpand
    omega
  have hBgrow : 0 < B.card → 4 ≤ (exteriorClosedNeighborhood G Q B).card := by
    intro hb
    let : Nonempty B := (Finset.card_pos.mp hb).to_subtype
    have hpos := indepNum_pos_of_nonempty (G.induce (B : Set V))
    have hg := one_clique_neighbor_expansion (Finset.card_pos.mp hb) hBQ hcoverB hexpand
    omega
  have hDne : D.Nonempty := Finset.card_pos.mp (by have := hlow 2; change 2 ≤ D.card at this; omega)
  let : Nonempty D := hDne.to_subtype
  have hDpos := indepNum_pos_of_nonempty (G.induce (D : Set V))
  have hDgrow := one_clique_neighbor_expansion hDne hDQ hcoverD hexpand
  have hDfour : 4 ≤ (exteriorClosedNeighborhood G Q D).card := by omega
  have hU0card : I.card + A.card = (U 0).card := by
    have h := Finset.card_sdiff_add_card_eq_card hI0
    change A.card + I.card = (U 0).card at h
    omega
  have hU1card : I.card + B.card = (U 1).card := by
    have h := Finset.card_sdiff_add_card_eq_card hI1
    change B.card + I.card = (U 1).card at h
    omega
  obtain ⟨hIcard, hAcard, hBcard⟩ := overlapping_triangle_card_arithmetic
    (show 1 ≤ I.card from Finset.card_pos.mpr hIne)
    (by rw [hU0card]; exact hlow 0) (by rw [hU1card]; exact hlow 1)
    hIgrow hAgrow hBgrow hDfour hsum
  have hU0I : U 0 = I := Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hAcard)) hI0
  have hU1I : U 1 = I := Finset.Subset.antisymm
    (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hBcard)) hI1
  have hDα : (G.induce (D : Set V)).indepNum ≤ 1 := by omega
  have hDcomplete := complete_of_indepNum_le_one hDα
  have hDclique : G.IsClique (D : Set V) := by
    intro u hu v hv huv
    have h : (G.induce (D : Set V)).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
      rw [hDcomplete]
      exact fun he => huv (congrArg Subtype.val he)
    exact h
  have hDcard : D.card = 2 := by
    have hupper := exterior_clique_card_le_two (hqQ 2) (fun _ h => h) hDclique hω
    change D.card ≤ 2 at hupper
    have hlower := hlow 2
    change 2 ≤ D.card at hlower
    omega
  have hIlower : 7 ≤ (exteriorClosedNeighborhood G Q I).card := by omega
  have hU0card2 : (U 0).card = 2 := by rwa [hU0I]
  have hU0ind : G.IsIndepSet (U 0 : Set V) := by rw [hU0I]; exact hIind
  have hU0lower : 7 ≤ (exteriorClosedNeighborhood G Q (U 0)).card := by rw [hU0I]; exact hIlower
  exact ⟨hU0card2, hU0I.trans hU1I.symm, hU0ind, hDcard, hDclique, hU0lower⟩

end CycleClique.Construction

end OAI
