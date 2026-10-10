import OAI.Probability.FreeIsing.Posterior.ComponentPosteriorStationarity

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem componentObservationField_eq_own_sup_children
    {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (c : Fin d) :
    selectedObservationField F (componentIndexVertex (c := c)) =
      selectedObservationField F (fun _ : Unit =>
        (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d)) ⊔
      ⨆ a : {a : Fin d // c ≠ a}, selectedObservationField F (childComponentIndexVertex c a.1) := by
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi, iSup_const]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, w, hlen, hchain⟩
    cases w with
    | nil => exact le_sup_left
    | cons a w =>
        have hca : c ≠ a := (List.isChain_cons_cons.mp hchain).1
        let u : ComponentIndex a := ⟨w.length, ⟨w, rfl, hchain.tail⟩⟩
        have hv : componentIndexVertex (c := c) ⟨n, ⟨a :: w, hlen, hchain⟩⟩ =
            childComponentIndexVertex c a u := by
          apply Subtype.ext
          simp [childComponentIndexVertex_val hca, componentIndexVertex, componentVertex, u]
        rw [hv]
        exact le_sup_of_le_right (le_iSup_of_le (⟨a, hca⟩ : {a : Fin d // c ≠ a})
          (le_iSup_of_le u le_rfl))
  · apply sup_le
    · exact le_iSup_of_le (⟨0, ⟨[], rfl, List.IsChain.singleton c⟩⟩ : ComponentIndex c) le_rfl
    · apply iSup_le
      intro a
      apply iSup_le
      intro u
      let w : ComponentIndex c := ⟨u.1 + 1, ⟨a.1 :: u.2.1,
        by simp [u.2.2.1], List.isChain_cons_cons.mpr ⟨a.2, u.2.2.2⟩⟩⟩
      have hv : childComponentIndexVertex c a.1 u = componentIndexVertex w := by
        apply Subtype.ext
        simp [childComponentIndexVertex_val a.2, componentIndexVertex, componentVertex, w]
      rw [hv]
      exact le_iSup_of_le w le_rfl

end Problem367

end

end OAI
