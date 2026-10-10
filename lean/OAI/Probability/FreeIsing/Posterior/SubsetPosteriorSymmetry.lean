import OAI.Probability.FreeIsing.Posterior.Symmetry

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.PlantedSymmetry

theorem measurable_plantedFlip_selected_observationSigma
    {ι κ : Type*} (v : ι → κ) (t : ℝ) :
    Measurable[
      MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance,
      MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance]
      (plantedFlipEquiv κ) := by
  let X : ((κ → IsingSpin) × (κ → ℝ)) → (ι → ℝ) :=
    fun p i => observation t p (v i)
  apply measurable_comap_iff.mpr
  have heq : X ∘ plantedFlipEquiv κ = fun p => -X p := by
    funext p i
    exact congrFun (observation_flip t p) (v i)
  change Measurable[MeasurableSpace.comap X inferInstance] (X ∘ plantedFlipEquiv κ)
  rw [heq]
  exact (comap_measurable X).neg

theorem selectedPosterior_flip_ae
    {ι κ : Type*} {mu : Measure (κ → IsingSpin)} {nu : Measure (κ → ℝ)}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu)
    (v : ι → κ) (t : ℝ) (r : κ) :
    ((mu.prod nu)[fun p => spinSign (p.1 r) |
      MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance]) ∘
        plantedFlipEquiv κ =ᵐ[mu.prod nu]
      -((mu.prod nu)[fun p => spinSign (p.1 r) |
        MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance]) := by
  have hX : Measurable (fun p i => observation t p (v i)) :=
    Measurable.of_eval (fun i => (measurable_pi_apply (v i)).comp
      (measurable_observation t))
  have hnat := condExp_comp_measurePreserving_equiv hX.comap_le (plantedFlipEquiv κ)
    (product_measurePreserving_flip hmu hnu)
    (measurable_plantedFlip_selected_observationSigma v t)
    (measurable_plantedFlip_selected_observationSigma v t)
    (integrable_plantedSpin (mu.prod nu) r)
  have hodd : (fun p : (κ → IsingSpin) × (κ → ℝ) => spinSign (p.1 r)) ∘
      plantedFlipEquiv κ = -(fun p : (κ → IsingSpin) × (κ → ℝ) => spinSign (p.1 r)) := by
    funext p
    cases hs : p.1 r <;>
      simp [plantedFlipEquiv, flipConfig, IsingSpin.flip, spinSign, hs]
  rw [hodd] at hnat
  exact hnat.trans (condExp_neg _ _)

theorem selectedPosteriorLaw_neg_invariant
    {ι κ : Type*} {mu : Measure (κ → IsingSpin)} {nu : Measure (κ → ℝ)}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : mu.map flipConfig = mu) (hnu : nu.map Neg.neg = nu)
    (v : ι → κ) (t : ℝ) (r : κ) :
    (((mu.prod nu).map ((mu.prod nu)[fun p => spinSign (p.1 r) |
      MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance])).map Neg.neg) =
      (mu.prod nu).map ((mu.prod nu)[fun p => spinSign (p.1 r) |
        MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance]) := by
  have hX : Measurable (fun p i => observation t p (v i)) :=
    Measurable.of_eval (fun i => (measurable_pi_apply (v i)).comp
      (measurable_observation t))
  exact FactorTransport.map_invariant_of_ae_equivariant
    (product_measurePreserving_flip hmu hnu) measurable_neg
    (stronglyMeasurable_condExp.measurable.mono hX.comap_le le_rfl)
    (selectedPosterior_flip_ae hmu hnu v t r)

theorem freeIsing_gaussian_selectedPosteriorLaw_neg_invariant
    {d : ℕ} {theta : ℝ} {ι : Type*}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (v : ι → TreeVertex d) (t : ℝ) (variance : NNReal) (r : TreeVertex d) :
    (((mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map
      ((mu.prod (gaussianNoiseLaw (TreeVertex d) variance))[fun p => spinSign (p.1 r) |
        MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance])).map Neg.neg) =
      (mu.prod (gaussianNoiseLaw (TreeVertex d) variance)).map
        ((mu.prod (gaussianNoiseLaw (TreeVertex d) variance))[fun p => spinSign (p.1 r) |
          MeasurableSpace.comap (fun p i => observation t p (v i)) inferInstance]) := by
  let : IsFiniteMeasure mu :=
    hmu.finite_of_connected (ConnectedHull.hull ∅) (ConnectedHull.connected_hull ∅)
  exact selectedPosteriorLaw_neg_invariant hmu.flip_invariant
    (gaussianNoiseLaw_map_neg (TreeVertex d) variance) v t r

end Problem367.PlantedSymmetry

end

end OAI
