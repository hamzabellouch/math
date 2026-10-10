import OAI.Probability.FreeIsing.Trees.ConeComplementFusion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367
open PathSideBranches

theorem HasFreeIsingLaw.selected_gaussian_inside_subset_complement_field
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S T : Set (TreeVertex d)) (hS : S ⊆ cone r) (hT : T ⊆ (cone r)ᶜ)
    (hp : r ∈ S) (ht : parentVertex r ∈ T) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) r z)) =ᵐ[P]
      fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) r z) +
        statisticMessage (Real.tanh beta) (selectedPosterior P F
          (Subtype.val : T → TreeVertex d) (parentVertex r) z) := by
  obtain ⟨g, c, hr0, hpc, hgeo⟩ := exists_reroot_cone_complement r hr
  let q : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hq : q.1 ≠ [] := by simp [q]
  have hpq : parentVertex q = ConnectedHull.root d := by rfl
  have hS' : g.toEquiv '' S ⊆ (cone q)ᶜ := by
    rintro u ⟨v, hv, rfl⟩ hbad
    exact ((hgeo v).mpr hbad) (hS hv)
  have hT' : g.toEquiv '' T ⊆ cone q := by
    rintro u ⟨v, hv, rfl⟩
    exact (hgeo v).mp (hT hv)
  have hp' : parentVertex q ∈ g.toEquiv '' S := ⟨r, hp, hr0.trans hpq.symm⟩
  have ht' : q ∈ g.toEquiv '' T := ⟨parentVertex r, ht, hpc⟩
  have hbase := hμ.selected_gaussian_outside_subset_cone_field hbeta t q hq
    (g.toEquiv '' S) (g.toEquiv '' T) hS' hT' hp' ht'
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hb := hmp.quasiMeasurePreserving.ae_eq_comp hbase
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hST := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g (S ∪ T) r
  have hSS := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g S r
  have hTT := selectedPosterior_image_relabel_ae hμ (gaussianReal 0 t) hF g T (parentVertex r)
  filter_upwards [hb, hST, hSS, hTT] with z hz hst hss htt
  have hpc' : g.toEquiv (parentVertex r) = q := hpc
  rw [hpq, ← hr0, ← hpc', ← Set.image_union] at hz
  simp only [Function.comp_apply] at hst hss htt
  dsimp only [F, PlantedSymmetry.gaussianNoiseLaw] at hst hss htt hz ⊢
  simpa only [Function.comp_apply, hst, hss, htt] using hz

end Problem367

end

end OAI
