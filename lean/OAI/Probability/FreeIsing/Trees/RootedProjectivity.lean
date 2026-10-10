import OAI.Probability.FreeIsing.Estimates.FiniteWeightNormalization
import OAI.Probability.FreeIsing.Trees.Parents

namespace OAI

noncomputable section

namespace Problem367

theorem ConnectedFinset.exists_prunable_vertex_of_shared_min
    {d : ℕ} {D E : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hE : ConnectedFinset E) (hDE : D ⊆ E) {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (hne : D ≠ E) :
    ∃ v p : TreeVertex d, v ∈ E ∧ v ∉ D ∧ p ∈ E ∧ p ≠ v ∧
      ConnectedFinset (E.erase v) ∧ D ⊆ E.erase v ∧
      inducedEdges E = insert (p, v) (inducedEdges (E.erase v)) := by
  classical
  have hdiff : (E \ D).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hED
    exact hne (Finset.Subset.antisymm hDE hED))
  obtain ⟨v, hvdiff, hmax⟩ := Finset.exists_max_image (E \ D) (fun x => x.1.length) hdiff
  obtain ⟨hvE, hvD⟩ := Finset.mem_sdiff.mp hvdiff
  have hvr : v ≠ r := by
    intro h
    exact hvD (h ▸ hr)
  have hpE : parentVertex v ∈ E :=
    hE.parent_mem_of_ne_min (hDE hr) hmin hvE hvr
  have hvnil : v.1 ≠ [] := ConnectedFinset.ne_nil_of_ne_min hmin hvE hvr
  have hpv : treeAdj (parentVertex v) v := treeAdj_parentVertex hvnil
  have hplen : (parentVertex v).1.length < v.1.length := by
    rw [parentVertex_length]
    have : 0 < v.1.length := List.length_pos_iff.mpr hvnil
    omega
  have hleaf : ∀ x ∈ E, treeAdj v x → x = parentVertex v := by
    intro x hx hadj
    rcases treeAdj_length hadj with hlen | hlen
    · have hxD : x ∈ D := by
        by_contra hxD
        have hbound := hmax x (Finset.mem_sdiff.mpr ⟨hx, hxD⟩)
        omega
      have hxr : x ≠ r := by
        intro h
        subst x
        have := hmin v hvE
        omega
      have hpD := hD.parent_mem_of_ne_min hr (fun y hy => hmin y (hDE hy)) hxD hxr
      have hparent : parentVertex x = v := treeAdj_parent_of_length_lt hadj (by omega)
      exact False.elim (hvD (hparent ▸ hpD))
    · exact (treeAdj_parent_of_length_lt (hadj.elim Or.inr Or.inl) (by omega)).symm
  have hDEerase : D ⊆ E.erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro h; exact hvD (h ▸ hx), hDE hx⟩
  have hconn : ConnectedFinset (E.erase v) :=
    connectedFinset_erase_of_leaf hE hvE ⟨r, hDEerase hr⟩
      (fun x hx y hy hvx hvy => (hleaf x hx hvx).trans (hleaf y hy hvy).symm)
  refine ⟨v, parentVertex v, hvE, hvD, hpE, ?_, hconn, hDEerase, ?_⟩
  · intro h
    have := congrArg (fun x : TreeVertex d => x.1.length) h
    omega
  · exact inducedEdges_eq_insert_erase_of_unique_lower_neighbor hvE hpE hpv hplen hleaf

theorem finiteFreeIsingPMF_map_subset_of_shared_min
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {D E : Finset (TreeVertex d)} (hD : ConnectedFinset D) (hE : ConnectedFinset E)
    (hDE : D ⊆ E) {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) :
    (finiteFreeIsingPMF hlo hhi E hE).map (Finset.restrict₂ (π := fun _ => IsingSpin) hDE) =
      finiteFreeIsingPMF hlo hhi D hD := by
  classical
  revert hE hDE hmin
  refine Finset.strongInductionOn E ?_
  intro E ih hE hDE hmin
  by_cases heq : D = E
  · subst E
    have hf : (Finset.restrict₂ (π := fun _ => IsingSpin) hDE : (D → IsingSpin) → (D → IsingSpin)) = id := rfl
    rw [hf, PMF.map_id]
  · obtain ⟨v, p, hvE, _, _, hpne, hEr, hDEr, hedges⟩ :=
      hD.exists_prunable_vertex_of_shared_min hE hDE hr hmin heq
    have hErE : E.erase v ⊆ E := Finset.erase_subset _ _
    have hmap : (finiteFreeIsingPMF hlo hhi E hE).map (Finset.restrict₂ (π := fun _ => IsingSpin) hErE) =
        finiteFreeIsingPMF hlo hhi (E.erase v) hEr :=
      finiteFreeIsingPMF_map_erase_of_edges hlo hhi hE hvE hpne hEr hedges
    calc
      _ = ((finiteFreeIsingPMF hlo hhi E hE).map (Finset.restrict₂ (π := fun _ => IsingSpin) hErE)).map
          (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr) := by
        rw [PMF.map_comp]
        rfl
      _ = (finiteFreeIsingPMF hlo hhi (E.erase v) hEr).map (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr) := by
        rw [hmap]
      _ = _ := ih (E.erase v) (Finset.erase_ssubset hvE) hEr hDEr
        (fun x hx => hmin x (hErE hx))

theorem finiteFreeIsingPMF_map_subset_of_root_mem
    {d : ℕ} {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {D E : Finset (TreeVertex d)} (hD : ConnectedFinset D) (hE : ConnectedFinset E)
    (hDE : D ⊆ E) {r : TreeVertex d} (hr : r ∈ D) (hrnil : r.1 = []) :
    (finiteFreeIsingPMF hlo hhi E hE).map (Finset.restrict₂ (π := fun _ => IsingSpin) hDE) =
      finiteFreeIsingPMF hlo hhi D hD :=
  finiteFreeIsingPMF_map_subset_of_shared_min hlo hhi hD hE hDE hr
    (fun x _ => by simp [hrnil])

end Problem367

end

end OAI
