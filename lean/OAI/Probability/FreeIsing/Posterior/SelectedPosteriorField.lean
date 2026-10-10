import OAI.Probability.FreeIsing.Brownian.PosteriorField
import OAI.Probability.FreeIsing.Posterior.InfinitePosteriorField
import OAI.Probability.FreeIsing.Posterior.SelectedPosteriorStationarity

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem condExp_tanh_bounds_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K)) :
    ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₁]) ω ∧
      (μ[f | m₁]) ω ≤ Real.tanh (X ω + K) := by
  have h₁ : m₁ ≤ m := h₁₂.trans h₂
  have hL : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω - K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.sub stronglyMeasurable_const)
  have hU : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω + K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.add stronglyMeasurable_const)
  have iL : Integrable (fun ω => Real.tanh (X ω - K)) μ := by
    apply Integrable.of_bound (hL.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω - K)).le
  have iU : Integrable (fun ω => Real.tanh (X ω + K)) μ := by
    apply Integrable.of_bound (hU.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω + K)).le
  have hlo := condExp_mono (m := m₁) iL integrable_condExp
    (hb.mono fun ω hω => hω.1)
  have hhi := condExp_mono (m := m₁) integrable_condExp iU
    (hb.mono fun ω hω => hω.2)
  rw [condExp_of_stronglyMeasurable h₁ hL iL] at hlo
  rw [condExp_of_stronglyMeasurable h₁ hU iU] at hhi
  filter_upwards [hlo, hhi, condExp_condExp_of_le (f := f) h₁₂ h₂] with ω hLω hUω hTω
  rw [hTω] at hLω hUω
  exact ⟨hLω, hUω⟩

theorem condExp_field_bound_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, (μ[f | m₂]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₂]) ω) - X ω| ≤ K) :
    ∀ᵐ ω ∂μ, (μ[f | m₁]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₁]) ω) - X ω| ≤ K := by
  have hmono : Monotone Real.tanh := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hasDerivAt_tanh_response x).differentiableAt
    · intro x
      rw [(hasDerivAt_tanh_response x).deriv]
      exact (sub_pos.mpr (Real.tanh_sq_lt_one x)).le
  have hs : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K) := by
    filter_upwards [hb] with ω hω
    have hlo := hmono (show X ω - K ≤ Real.artanh ((μ[f | m₂]) ω) by
      linarith [(abs_le.mp hω.2).1])
    have hhi := hmono (show Real.artanh ((μ[f | m₂]) ω) ≤ X ω + K by
      linarith [(abs_le.mp hω.2).2])
    rw [Real.tanh_artanh hω.1] at hlo hhi
    exact ⟨hlo, hhi⟩
  filter_upwards [condExp_tanh_bounds_of_le (m := m) μ h₁₂ h₂ hX hs] with ω hω
  have h := posterior_field_limit_of_tanh_bounds
    (u := fun _ : ℕ => (μ[f | m₁]) ω) tendsto_const_nhds (fun _ => hω)
  exact ⟨h.1, h.2.1⟩

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_bound
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) :
    ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p) -
          PlantedSymmetry.observation t p r| ≤ (d : ℝ) * β := by
  let := hμ.isProbabilityMeasure
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hsub : selectedObservationField F v ≤
      PlantedSymmetry.observationSigma (TreeVertex d) t := by
    change selectedObservationField F v ≤ selectedObservationField F id
    apply selectedObservationField_le_of_range_subset F
    intro w hw
    exact ⟨w, rfl⟩
  have hX : StronglyMeasurable[selectedObservationField F v]
      (fun p => PlantedSymmetry.observation t p r) := by
    obtain ⟨i, rfl⟩ := hr
    exact ((measurable_pi_apply i).comp (comap_measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun j => F (p.1 (v j)) (p.2 (v j))))).stronglyMeasurable
  exact condExp_field_bound_of_le
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hsub
    (PlantedSymmetry.observationSigma_le (TreeVertex d) t) hX
    (hμ.gaussian_posterior_field_bound hβ t r)

theorem HasFreeIsingLaw.selected_brownian_past_posterior_field_bound
    {d : ℕ} {ι Ω : Type*} [MeasurableSpace Ω] {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (ν : Measure Ω) {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B ν) (hmB : ∀ t, Measurable (B t))
    (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d) (hr : r ∈ Set.range v) :
    let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let F : IsingSpin → Ω → (Set.Iic t → ℝ) :=
      fun s z u => (u.1 : ℝ) * spinSign s + B u.1 z
    ∀ᵐ p ∂ρ, selectedPosterior ρ F v r p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (selectedPosterior ρ F v r p) -
        ((t : ℝ) * spinSign (p.1 r) + B t (p.2 r))| ≤ (d : ℝ) * β := by
  let := hμ.isProbabilityMeasure
  let := hB.isGaussianProcess.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let F : IsingSpin → Ω → (Set.Iic t → ℝ) :=
    fun s z u => (u.1 : ℝ) * spinSign s + B u.1 z
  have hF : Measurable (Function.uncurry F) := by
    have hs : Measurable spinSign := by intro s hs; trivial
    exact Measurable.of_eval fun time =>
      ((hs.comp measurable_fst).const_mul (time.1 : ℝ)).add ((hmB time.1).comp measurable_snd)
  have hsub : selectedObservationField F v ≤ selectedObservationField F id := by
    apply selectedObservationField_le_of_range_subset F
    intro w hw
    exact ⟨w, rfl⟩
  have hX : StronglyMeasurable[selectedObservationField F v]
      (fun p => (t : ℝ) * spinSign (p.1 r) + B t (p.2 r)) := by
    obtain ⟨i, rfl⟩ := hr
    exact ((measurable_pi_apply (⟨t, by simp⟩ : Set.Iic t)).comp
      ((measurable_pi_apply i).comp (comap_measurable
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → Ω) =>
          fun j => F (p.1 (v j)) (p.2 (v j)))))).stronglyMeasurable
  exact condExp_field_bound_of_le ρ hsub (selectedObservationField_le hF id) hX
    (hμ.brownian_past_posterior_field_bound hβ (fun _ => ν)
      (fun _ => hB) (fun _ u => hmB u) t r)

end Problem367

end

end OAI
