import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Posterior.PlantedStationarity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

@[reducible] def selectedObservationField {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) :
    MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
  MeasurableSpace.comap (fun p i => F (p.1 (v i)) (p.2 (v i))) inferInstance

def selectedPosterior {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) → ℝ :=
  rho[fun p => spinSign (p.1 r) | selectedObservationField F v]

theorem selectedObservationField_le {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) : selectedObservationField F v ≤
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) := by
  have hobs : Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun i => F (p.1 (v i)) (p.2 (v i))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact hF.comp (show Measurable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (p.1 (v i), p.2 (v i))) by fun_prop)
  exact hobs.comap_le

theorem measurable_selectedPosterior {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    Measurable (selectedPosterior rho F v r) :=
  stronglyMeasurable_condExp.measurable.mono (selectedObservationField_le hF v) le_rfl

theorem selectedObservationField_comap_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (g : TreeAut d) :
    (selectedObservationField F v).comap (Prod.map (relabel g) (relabel g)) =
      selectedObservationField F (fun i => g.toEquiv.symm (v i)) := by
  unfold selectedObservationField
  rw [MeasurableSpace.comap_comp]
  rfl

theorem selectedObservationField_le_of_range_subset {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hv : Set.range v ⊆ Set.range w) :
    selectedObservationField F v ≤ selectedObservationField F w := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
    selectedObservationField F w
  have hobs : Measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun i => F (p.1 (v i)) (p.2 (v i))) := by
    apply measurable_pi_iff.mpr
    intro i
    obtain ⟨j, hj⟩ := hv ⟨i, rfl⟩
    have hm : Measurable
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          F (p.1 (w j)) (p.2 (w j))) :=
      (measurable_pi_apply j).comp (comap_measurable
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          fun k => F (p.1 (w k)) (p.2 (w k))))
    simpa only [hj] using hm
  exact hobs.comap_le

theorem selectedObservationField_eq_of_range_eq {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hvw : Set.range v = Set.range w) :
    selectedObservationField F v = selectedObservationField F w :=
  le_antisymm (selectedObservationField_le_of_range_subset F hvw.subset)
    (selectedObservationField_le_of_range_subset F hvw.symm.subset)

theorem selectedPosterior_relabel_ae {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
        Prod.map (relabel g) (relabel g) =ᵐ[mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))]
      selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r) := by
  let := hmu.isProbabilityMeasure
  let rho := mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) rho := by
    apply Integrable.of_bound
      ((hsign.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hCE := condExp_comp_measurePreserving rho rho
    (Prod.map (relabel g) (relabel g))
    (PlantedStationarity.measurePreserving_planted_relabel hmu nu g)
    (selectedObservationField F v) (selectedObservationField_le hF v) hi
  rw [selectedObservationField_comap_relabel] at hCE
  exact hCE.symm

theorem selectedPosterior_identDistrib_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have hm := measurable_selectedPosterior
    (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) hF v r
  refine ⟨hm.aemeasurable, (measurable_selectedPosterior _ hF _ _).aemeasurable, ?_⟩
  have hCE := selectedPosterior_relabel_ae hmu nu hF v r g
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hmu nu g
  calc
    _ = Measure.map
        (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
          Prod.map (relabel g) (relabel g))
        (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
      rw [← Measure.map_map hm hmp.measurable, hmp.map_eq]
    _ = _ := Measure.map_congr hCE

theorem selectedPosterior_secondMoment_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    (∫ p, selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      F v r p ^ 2 ∂mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) =
    ∫ p, selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r) p ^ 2
        ∂mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)) :=
  ((selectedPosterior_identDistrib_relabel hmu nu hF v r g).comp
    (show Measurable (fun u : ℝ => u ^ 2) by fun_prop)).integral_eq

theorem selectedPosterior_identDistrib_of_range_relabel {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (w : κ → TreeVertex d) (r s : TreeVertex d) (g : TreeAut d)
    (hregion : Set.range (fun i => g.toEquiv.symm (v i)) = Set.range w)
    (hroot : g.toEquiv.symm r = s) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F w s)
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have h := selectedPosterior_identDistrib_relabel hmu nu hF v r g
  simpa only [selectedPosterior, selectedObservationField_eq_of_range_eq F hregion, hroot] using h

end Problem367

end

end OAI
