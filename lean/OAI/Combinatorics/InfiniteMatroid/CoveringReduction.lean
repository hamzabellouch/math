import OAI.Combinatorics.InfiniteMatroid.Waves

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

lemma packingCovering_of_wave_covering {α : Type*} {M : Bool → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) {W : Set α × (Bool → Set α)}
    (hW : Wave M F W) (hC : FamilyCovering (F \ W.1) (fun i ↦ M i ／ W.1)) :
    HasPackingCovering (M false) (M true) := by
  obtain ⟨I, hI, hcov⟩ := hC
  have hfull : I false ∪ I true = F \ W.1 := by
    rw [← hcov]
    ext x
    simp only [mem_union, mem_iUnion]
    exact ⟨fun h ↦ h.elim (fun hx ↦ ⟨false, hx⟩) (fun hx ↦ ⟨true, hx⟩),
      fun ⟨i, hi⟩ ↦ by cases i <;> simp_all⟩
  have hsub : ∀ i, I i ⊆ F \ W.1 := by
    intro i
    simpa [hE] using (hI i).subset_ground
  have hcont : ∀ i, (contractOnto (M i) (F \ W.1)).Indep (I i) := by
    intro i
    rw [← hE i, contractOnto_ground_sdiff]
    exact hI i
  refine ⟨W.1, F \ W.1, W.2 false, W.2 true, I false, I true,
    disjoint_sdiff_right, ?_, (hE true).trans (hE false).symm,
    hW.2.1 false, hW.2.1 true, hW.2.2.1 Bool.false_ne_true, ?_, ?_,
    hsub false, hsub true, hcont false, hcont true, hfull⟩
  · rw [hE false]
    exact union_sdiff_cancel hW.1
  · exact ((M false).restrict_spanning_iff (hW.2.1 false)
      (by rw [hE]; exact hW.1)).mpr (hW.2.2.2 false)
  · exact ((M true).restrict_spanning_iff (hW.2.1 true)
      (by rw [hE]; exact hW.1)).mpr (hW.2.2.2 true)

theorem separate_covering_of_no_packingCovering {α : Type*} {M : Bool → Matroid α}
    {F : Set α} (hE : ∀ i, (M i).E = F)
    (hno : ¬ HasPackingCovering (M false) (M true)) :
    ∃ (C : Set α) (N : Bool → Matroid α),
      (∀ i, (N i).E = C) ∧ ¬ FamilyCovering C N ∧
      (∀ Y ⊆ C, FamilyPacking (fun i ↦ N i ↾ Y) →
        FamilyCovering Y (fun i ↦ N i ↾ Y)) := by
  obtain ⟨W, hW⟩ := exists_maximal_wave M F
  refine ⟨F \ W.1, fun i ↦ M i ／ W.1, ?_, ?_, residual_covering_condition hE hW⟩
  · simp [hE]
  · exact fun h ↦ hno (packingCovering_of_wave_covering hE hW.1 h)

end InfiniteMatroidCounterexample

end OAI
