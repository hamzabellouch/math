import OAI.Probability.FreeIsing.Trees.ConeComponentAttenuation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.selectedPosterior_parent_cone
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (r : TreeVertex d) (hr : r.1 ≠ []) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : cone r → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => theta * selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hparent : g.toEquiv.symm (RootedBroadcast.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
    rfl
  have hchild : g.toEquiv.symm (RootedBroadcast.branchRoot c) = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hc]
    rfl
  have hfield := selectedObservationField_eq_of_range_eq F
    (range_relabel_componentIndexVertex_eq_cone g r c hgeo)
  have hb := hμ.selectedPosterior_root_component h0 h1 ν hF c
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ ν g
  have hbp := hmp.quasiMeasurePreserving.ae_eq_comp hb
  have hpull := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := c)) (RootedBroadcast.root d) g
  have hcpull := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) g
  filter_upwards [hbp, hpull, hcpull] with z hbz hpz hcz
  have h := hpz.symm.trans (hbz.trans (congrArg (fun q : ℝ => theta * q) hcz))
  simpa only [selectedPosterior, hfield, hparent, hchild] using h

end Problem367

end

end OAI
