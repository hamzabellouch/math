import OAI.Probability.FreeIsing.Estimates.InfiniteComponentCavity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry CavityFieldLimit

theorem HasFreeIsingLaw.infiniteGibbsSpinMean_gaussian_relabel
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (t : ℝ≥0)
    (g : TreeAut d) (v : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteGibbsSpinMean β v (relabel g (observation t p)) =
      infiniteGibbsSpinMean β (g.toEquiv.symm v) (observation t p) := by
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) := by
    have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul (t : ℝ)).add measurable_snd
  have hfield : selectedObservationField F (fun i => g.toEquiv.symm i) =
      selectedObservationField F id := by
    apply selectedObservationField_eq_of_range_eq
    simp only [Equiv.range_eq_univ, Set.range_id]
  have hpost := selectedPosterior_relabel_ae hμ (gaussianReal 0 t) hF id v g
  simp only [id_eq, selectedPosterior, hfield] at hpost
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ
    (gaussianReal 0 t) g
  have hleft := hmp.quasiMeasurePreserving.ae
    (hμ.infiniteGibbsSpinMean_eq_posterior t v)
  filter_upwards [hleft, hpost,
    hμ.infiniteGibbsSpinMean_eq_posterior t (g.toEquiv.symm v)] with p hl hp hr
  exact hl.trans (hp.trans hr.symm)

theorem HasFreeIsingLaw.infiniteCavityField_gaussian_relabel
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (t : ℝ≥0)
    (g : TreeAut d) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ v w (relabel g (observation t p)) =
      infiniteCavityField hβ (g.toEquiv.symm v) (g.toEquiv.symm w)
        (observation t p) := by
  filter_upwards [hμ.infiniteGibbsSpinMean_gaussian_relabel t g v,
    hμ.infiniteGibbsSpinMean_gaussian_relabel t g w] with p hv hw
  simp only [infiniteCavityField, CavityArray.field, hv, hw]

theorem HasFreeIsingLaw.infiniteCavityField_eq_relabelled_component
    {d : ℕ} {β : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh β) μ) (hβ : 0 ≤ β) (t : ℝ≥0)
    (g : TreeAut d) (c : Fin d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      infiniteCavityField hβ (g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩)
        (g.toEquiv.symm (ConnectedHull.root d)) (observation t p) =
      Real.artanh (selectedPosterior (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z)
        (fun i : ComponentIndex c => g.toEquiv.symm (componentIndexVertex i))
        (g.toEquiv.symm ⟨[c], List.IsChain.singleton c⟩) p) := by
  have hs : Measurable spinSign := by intro s hs; trivial
  have hF : Measurable (Function.uncurry
      (fun (s : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign s + z)) :=
    ((hs.comp measurable_fst).const_mul (t : ℝ)).add measurable_snd
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ
    (gaussianReal 0 t) g
  have hroot := hmp.quasiMeasurePreserving.ae
    (hμ.infiniteCavityField_eq_component hβ t c)
  have hpost := selectedPosterior_relabel_ae hμ (gaussianReal 0 t) hF
    (componentIndexVertex (c := c)) ⟨[c], List.IsChain.singleton c⟩ g
  filter_upwards [hroot, hpost, hμ.infiniteCavityField_gaussian_relabel hβ t g
    ⟨[c], List.IsChain.singleton c⟩ (ConnectedHull.root d)] with p hr hp hn
  exact hn.symm.trans (hr.trans (congrArg Real.artanh hp))

end Problem367

end

end OAI
