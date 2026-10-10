import OAI.Probability.FreeIsing.Cavity.ArtanhFusion
import OAI.Probability.FreeIsing.Estimates.SelectedComponentFusion
import OAI.Probability.FreeIsing.Posterior.ConePosteriorRegression
import OAI.Probability.FreeIsing.Trees.SelectedPathLocality

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.selected_gaussian_outside_cone_fusion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hp : parentVertex r ∈ S) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    selectedPosterior P F (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => binaryFusion
        (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)
        (Real.tanh beta * selectedPosterior P F
          (Subtype.val : cone r → TreeVertex d) r z) := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let X := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : S => F (z.1 i.1) (z.2 i.1)
  let Y := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : cone r => F (z.1 i.1) (z.2 i.1)
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hXout : Measurable[noisyRegionSigma (A := ℝ) (cone r)ᶜ] X :=
    (comap_measurable X).mono
      ((selectedObservationField_le_noisyRegionSigma hF S).trans
        (noisyRegionSigma_mono hS)) le_rfl
  have hYin : Measurable[noisyRegionSigma (A := ℝ) (cone r)] Y :=
    (comap_measurable Y).mono
      (selectedObservationField_le_noisyRegionSigma hF (cone r)) le_rfl
  have hInd := hμ.condIndepFun_noisy_cone_observables
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) r hr X Y hXout hYin
  have hreg : selectedPosterior P F (Subtype.val : cone r → TreeVertex d)
      (parentVertex r) =ᵐ[P] fun z => Real.tanh beta *
        selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z :=
    hμ.selectedPosterior_parent_cone
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) hF r hr
  have hL : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hQ : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : cone r → TreeVertex d) r ⟨⟨r, List.prefix_refl _⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hR : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : cone r → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hreg, hQ] with z hz hq
    rw [hz, abs_mul]
    exact (mul_le_mul_of_nonneg_left hq.le (abs_nonneg (Real.tanh beta))).trans_lt
      (by simpa using Real.abs_tanh_lt_one beta)
  have h := condExp_spin_comap_sup_eq_binaryFusion
    ((measurable_pi_apply (parentVertex r)).comp measurable_fst) hX hY
    (hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) _) hInd hL hR
  dsimp only
  unfold selectedPosterior
  rw [selectedObservationField_region_union]
  filter_upwards [h, hreg] with z hz hregz
  exact hz.trans (congrArg (binaryFusion
    (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)) hregz)

theorem HasFreeIsingLaw.selected_gaussian_outside_cone_field
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hp : parentVertex r ∈ S) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)) =ᵐ[P]
      fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) (parentVertex r) z) +
        statisticMessage (Real.tanh beta) (selectedPosterior P F
          (Subtype.val : cone r → TreeVertex d) r z) := by
  have h := hμ.selected_gaussian_outside_cone_fusion hbeta t r hr S hS hp
  have hL := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩
  have hQ := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : cone r → TreeVertex d) r ⟨⟨r, List.prefix_refl _⟩, rfl⟩
  filter_upwards [h, hL, hQ] with z hz hl hq
  rw [hz]
  exact artanh_binaryFusion (abs_lt.mpr hl.1)
    (binaryFusion_abs_mul_lt_one (Real.abs_tanh_lt_one beta) (abs_lt.mpr hq.1))

end Problem367

end

end OAI
