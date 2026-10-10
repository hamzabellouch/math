import OAI.Probability.FreeIsing.Posterior.FieldL2Limit
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorField

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

def selectedObservationExhaustion {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (D : ℕ → Finset ι) (hD : Monotone D) :
    Filtration ℕ (inferInstance : MeasurableSpace
      ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) where
  seq n := selectedObservationField F (fun i : D n => v i.1)
  mono' n m hnm := selectedObservationField_le_of_range_subset F (by
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, hD hnm i.2⟩, rfl⟩)
  le' n := selectedObservationField_le hF _

theorem selectedObservationExhaustion_iSup {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (D : ℕ → Finset ι) (hD : Monotone D)
    (hex : ∀ i, ∃ n, i ∈ D n) :
    (⨆ n, selectedObservationExhaustion F hF v D hD n) =
      selectedObservationField F v := by
  change (⨆ n, selectedObservationField F (fun i : D n => v i.1)) = _
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro n
    apply iSup_le
    intro i
    exact le_iSup_of_le i.1 le_rfl
  · apply iSup_le
    intro i
    obtain ⟨n, hn⟩ := hex i
    exact le_iSup_of_le n (le_iSup_of_le (⟨i, hn⟩ : D n) le_rfl)

private theorem tanh_bounds_of_interior_field_bound {z x K : ℝ}
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) (h : |Real.artanh z - x| ≤ K) :
    Real.tanh (x - K) ≤ z ∧ z ≤ Real.tanh (x + K) := by
  constructor
  · apply (Real.artanh_le_artanh_iff
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩ hz).mp
    rw [Real.artanh_tanh]
    linarith [(abs_le.mp h).1]
  · apply (Real.artanh_le_artanh_iff hz
      ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩).mp
    rw [Real.artanh_tanh]
    linarith [(abs_le.mp h).2]

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_limit
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (D : ℕ → Finset ι) (hD : Monotone D) (hex : ∀ i, ∃ n, i ∈ D n)
    (hr : ∀ n, r ∈ Set.range (fun i : D n => v i.1)) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (∀ᵐ p ∂ρ, Tendsto
      (fun n => Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p))
      atTop (𝓝 (Real.artanh (selectedPosterior ρ F v r p)))) ∧
    Tendsto (fun n => ∫ p,
      (Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p) -
        Real.artanh (selectedPosterior ρ F v r p)) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let := hμ.isProbabilityMeasure
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) := by
    have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul (t : ℝ)).add measurable_snd
  let ℱ := selectedObservationExhaustion F hF v D hD
  have hsup : (⨆ n, ℱ n) = selectedObservationField F v :=
    selectedObservationExhaustion_iSup F hF v D hD hex
  have hb (n : ℕ) : ∀ᵐ p ∂ρ,
      Real.tanh (PlantedSymmetry.observation t p r - (d : ℝ) * β) ≤
        (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ∧
      (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ≤
        Real.tanh (PlantedSymmetry.observation t p r + (d : ℝ) * β) := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hβ t
      (fun i : D n => v i.1) r (hr n)] with p hp
    exact tanh_bounds_of_interior_field_bound hp.1 hp.2
  have hae := tendsto_posterior_fields_ae ρ ℱ
    (fun q => spinSign (q.1 r)) (fun p => PlantedSymmetry.observation t p r)
    ((d : ℝ) * β) hb
  have hL2 := tendsto_integral_sq_sub_posterior_fields ρ ℱ
    (fun q => spinSign (q.1 r)) (fun p => PlantedSymmetry.observation t p r) hb
  rw [hsup] at hae hL2
  exact ⟨hae.mono (fun p hp => hp.2.2), hL2⟩

theorem HasFreeIsingLaw.selected_brownian_past_posterior_field_limit
    {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω] {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (D : ℕ → Finset ι) (hD : Monotone D) (hex : ∀ i, ∃ n, i ∈ D n)
    (hr : ∀ n, r ∈ Set.range (fun i : D n => v i.1)) :
    let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F : IsingSpin → Ω → (Set.Iic t → ℝ) :=
      fun s z u => (u.1 : ℝ) * spinSign s + B u.1 z
    (∀ᵐ p ∂ρ, Tendsto
      (fun n => Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p))
      atTop (𝓝 (Real.artanh (selectedPosterior ρ F v r p)))) ∧
    Tendsto (fun n => ∫ p,
      (Real.artanh (selectedPosterior ρ F (fun i : D n => v i.1) r p) -
        Real.artanh (selectedPosterior ρ F v r p)) ^ 2 ∂ρ) atTop (𝓝 0) := by
  let := hμ.isProbabilityMeasure
  let := hB.isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let F : IsingSpin → Ω → (Set.Iic t → ℝ) :=
    fun s z u => (u.1 : ℝ) * spinSign s + B u.1 z
  have hF : Measurable (Function.uncurry F) := by
    have hs : Measurable spinSign := by intro s hs; trivial
    exact Measurable.of_eval fun u =>
      ((hs.comp measurable_fst).const_mul (u.1 : ℝ)).add ((hmB u.1).comp measurable_snd)
  let ℱ := selectedObservationExhaustion F hF v D hD
  have hsup : (⨆ n, ℱ n) = selectedObservationField F v :=
    selectedObservationExhaustion_iSup F hF v D hD hex
  let X := fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
    (t : ℝ) * spinSign (p.1 r) + B t (p.2 r)
  have hb (n : ℕ) : ∀ᵐ p ∂ρ,
      Real.tanh (X p - (d : ℝ) * β) ≤
        (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ∧
      (ρ[fun q => spinSign (q.1 r) | ℱ n]) p ≤
        Real.tanh (X p + (d : ℝ) * β) := by
    filter_upwards [hμ.selected_brownian_past_posterior_field_bound hβ ν hB hmB t
      (fun i : D n => v i.1) r (hr n)] with p hp
    exact tanh_bounds_of_interior_field_bound hp.1 hp.2
  have hae := tendsto_posterior_fields_ae ρ ℱ
    (fun q => spinSign (q.1 r)) X ((d : ℝ) * β) hb
  have hL2 := tendsto_integral_sq_sub_posterior_fields ρ ℱ
    (fun q => spinSign (q.1 r)) X hb
  rw [hsup] at hae hL2
  exact ⟨hae.mono (fun p hp => hp.2.2), hL2⟩

end Problem367

end

end OAI
