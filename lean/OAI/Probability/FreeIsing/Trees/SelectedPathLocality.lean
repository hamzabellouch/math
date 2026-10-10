import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorStationarity
import OAI.Probability.FreeIsing.Trees.NoisyPathLocality

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

open PathSideBranches

theorem selectedObservationField_region_union {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (S T : Set (TreeVertex d)) :
    selectedObservationField F (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) =
      selectedObservationField F (Subtype.val : S → TreeVertex d) ⊔
        selectedObservationField F (Subtype.val : T → TreeVertex d) := by
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro u
    rcases u.2 with hu | hu
    · exact le_sup_of_le_left (le_iSup_of_le (⟨u.1, hu⟩ : S) le_rfl)
    · exact le_sup_of_le_right (le_iSup_of_le (⟨u.1, hu⟩ : T) le_rfl)
  · apply sup_le
    · apply iSup_le
      intro u
      exact le_iSup_of_le (⟨u.1, Or.inl u.2⟩ : ↥(S ∪ T)) le_rfl
    · apply iSup_le
      intro u
      exact le_iSup_of_le (⟨u.1, Or.inr u.2⟩ : ↥(S ∪ T)) le_rfl

theorem selectedObservationField_le_noisyRegionSigma {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (S : Set (TreeVertex d)) :
    selectedObservationField F (Subtype.val : S → TreeVertex d) ≤
      noisyRegionSigma (A := A) S := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
    noisyRegionSigma (A := A) S
  have hobs : Measurable[noisyRegionSigma (A := A) S]
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : S => F (z.1 u.1) (z.2 u.1)) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp ((((measurable_pi_apply u).comp measurable_fst).prodMk
      ((measurable_pi_apply u).comp measurable_snd)).comp
        (comap_measurable (noisyRegionArray (A := A) S)))
  exact hobs.comap_le

theorem measurable_selectedPosterior_noisyRegion {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (S : Set (TreeVertex d)) (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := A) S]
      (selectedPosterior ρ F (Subtype.val : S → TreeVertex d) r) :=
  stronglyMeasurable_condExp.measurable.mono
    (selectedObservationField_le_noisyRegionSigma hF S) le_rfl

theorem measurable_selectedField_noisyRegion {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (S : Set (TreeVertex d)) (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := A) S]
      (fun z => Real.artanh (selectedPosterior ρ F (Subtype.val : S → TreeVertex d) r z)) := by
  have hA : Measurable Real.artanh := by
    unfold Real.artanh
    fun_prop
  exact hA.comp (measurable_selectedPosterior_noisyRegion ρ hF S r)

namespace PathSideBranches

def reducedForward {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length) :
    Set (TreeVertex d) :=
  cone (ConnectedHull.takeVertex v (i.1 + 1)) \ cone (sideVertex hd v i)

theorem target_mem_reducedForward {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : ConnectedHull.takeVertex v (i.1 + 1) ∈ reducedForward hd v i :=
  ⟨List.prefix_refl _, path_vertex_not_mem_sideCone hd v i _⟩

theorem reducedForward_subset_complement {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : reducedForward hd v i ⊆ (cone (sideVertex hd v i))ᶜ :=
  fun _ hu => hu.2

theorem forward_eq_reduced_union_side {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : cone (ConnectedHull.takeVertex v (i.1 + 1)) =
      reducedForward hd v i ∪ cone (sideVertex hd v i) := by
  ext u
  constructor
  · intro hu
    by_cases hs : u ∈ cone (sideVertex hd v i)
    · exact Or.inr hs
    · exact Or.inl ⟨hu, hs⟩
  · rintro (hu | hu)
    · exact hu.1
    · exact sideCone_subset_forward hd v i hu

theorem forwardObservationField_eq_reduced_sup_side {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length) :
    selectedObservationField F
      (Subtype.val : cone (ConnectedHull.takeVertex v (i.1 + 1)) → TreeVertex d) =
      selectedObservationField F (Subtype.val : reducedForward hd v i → TreeVertex d) ⊔
        selectedObservationField F (Subtype.val : cone (sideVertex hd v i) → TreeVertex d) := by
  rw [forward_eq_reduced_union_side hd v i]
  exact selectedObservationField_region_union F _ _

theorem measurable_later_selectedPosterior {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hd : 3 ≤ d) (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j)
    (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (selectedPosterior ρ F
        (Subtype.val : cone (ConnectedHull.takeVertex v (j.1 + 1)) → TreeVertex d) r) :=
  (measurable_selectedPosterior_noisyRegion ρ hF _ r).mono
    (noisyRegionSigma_mono (later_forward_subset_side_complement hd v hij)) le_rfl

theorem measurable_reduced_selectedField {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length) (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (fun z => Real.artanh (selectedPosterior ρ F
        (Subtype.val : reducedForward hd v i → TreeVertex d) r z)) :=
  (measurable_selectedField_noisyRegion ρ hF _ r).mono
    (noisyRegionSigma_mono (reducedForward_subset_complement hd v i)) le_rfl

theorem measurable_later_selectedPosterior_product {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length)
    (s : Finset (Fin v.1.length)) (hs : ∀ j ∈ s, i < j)
    (r : Fin v.1.length → TreeVertex d) (Φ : Fin v.1.length → ℝ → ℝ)
    (hΦ : ∀ j ∈ s, Measurable (Φ j)) :
    Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        ∏ j ∈ s, Φ j (selectedPosterior ρ F
          (Subtype.val : cone (ConnectedHull.takeVertex v (j.1 + 1)) → TreeVertex d) (r j) z)) := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
    noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ
  exact s.measurable_fun_prod (fun j hj => (hΦ j hj).comp
    (measurable_later_selectedPosterior ρ hF hd v (hs j hj) (r j)))

end PathSideBranches

end Problem367

end

end OAI
