import OAI.Probability.FreeIsing.Trees.ConeSelectedFusion

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PathSideBranches

local instance : Nonempty IsingSpin := ⟨.neg⟩

theorem HasFreeIsingLaw.condExp_selected_cone_field_attenuation_le_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hθ0 : 0 < Real.tanh beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hp : parentVertex r ∈ S) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    let field := fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)
    ∀ᵐ z ∂P,
      (P[fun z => responseAttenuation (Real.tanh beta) (field z) ^ 2 |
        noisyRegionSigma (A := ℝ) (cone r)ᶜ]) z ≤
        1 - ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          min (Real.sqrt (t : ℝ)) 1 := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hout : Measurable[noisyRegionSigma (A := ℝ) (cone r)ᶜ]
      (fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) (parentVertex r) z)) :=
    (measurable_selectedField_noisyRegion P hF S (parentVertex r)).mono
      (noisyRegionSigma_mono hS) le_rfl
  obtain ⟨shift, hs, hshift⟩ := hout.exists_eq_measurable_comp
  have hbase := ComponentSignalAttenuation.condExp_attenuation_le_critical_cone_complement
    hμ hθ0 (Real.tanh_lt_one beta) hcritical ht r hr
    (id : (({u : TreeVertex d // u ∉ cone r} → IsingSpin) ×
      ({u : TreeVertex d // u ∉ cone r} → ℝ)) → _) measurable_id shift hs
  have hfield := hμ.selected_gaussian_outside_cone_field hbeta t r hr S hS hp
  have hfactor : (fun z => responseAttenuation (Real.tanh beta)
      (Real.artanh (selectedPosterior P F
        (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)) ^ 2) =ᵐ[P]
      fun z => responseAttenuation (Real.tanh beta)
        (shift (noisyRegionArray (cone r)ᶜ z) + statisticMessage (Real.tanh beta)
          (selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z)) ^ 2 := by
    filter_upwards [hfield] with z hz
    have hs' := congrFun hshift z
    dsimp only [Function.comp_apply] at hs'
    rw [hz, hs']
  have hCE := condExp_congr_ae
    (m := noisyRegionSigma (A := ℝ) (cone r)ᶜ) hfactor
  filter_upwards [hbase, hCE] with z hz heq
  exact heq.trans_le hz

end Problem367

end

end OAI
