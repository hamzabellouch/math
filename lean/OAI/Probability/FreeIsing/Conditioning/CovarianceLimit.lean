import OAI.Probability.FreeIsing.Posterior.Limit

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def posteriorCovariance (μ : Measure Ω) (m : MeasurableSpace Ω)
    (f g : Ω → ℝ) : Ω → ℝ :=
  fun ω => μ[(fun x => f x * g x) | m] ω - μ[f | m] ω * μ[g | m] ω

lemma stronglyMeasurable_posteriorCovariance (μ : Measure Ω)
    (m : MeasurableSpace Ω) (f g : Ω → ℝ) :
    StronglyMeasurable[m] (posteriorCovariance (mΩ := mΩ) μ m f g) :=
  stronglyMeasurable_condExp.sub
    (stronglyMeasurable_condExp.mul stronglyMeasurable_condExp)

theorem tendsto_ae_posteriorCovariance (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorCovariance μ (F n) f g ω) atTop
      (𝓝 (posteriorCovariance μ (⨆ n, F n) f g ω)) := by
  exact tendsto_conditional_covariance_ae μ F f g

theorem ae_norm_posteriorCovariance_le (μ : Measure Ω)
    (m : MeasurableSpace Ω) {f g : Ω → ℝ} {R S : ℝ}
    (hR : 0 ≤ R) (_hS : 0 ≤ S)
    (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R) (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ S) :
    ∀ᵐ ω ∂μ, ‖posteriorCovariance (mΩ := mΩ) μ m f g ω‖ ≤ 2 * R * S := by
  have hfg : ∀ᵐ ω ∂μ, ‖f ω * g ω‖ ≤ R * S := by
    filter_upwards [hf, hg] with ω hfω hgω
    rw [norm_mul]
    exact mul_le_mul hfω hgω (norm_nonneg _) hR
  filter_upwards [ae_bdd_norm_condExp_of_ae_bdd_norm (m := m) hf,
    ae_bdd_norm_condExp_of_ae_bdd_norm (m := m) hg,
    ae_bdd_norm_condExp_of_ae_bdd_norm (m := m) hfg] with ω hfω hgω hfgω
  calc
    ‖posteriorCovariance (mΩ := mΩ) μ m f g ω‖ ≤
        ‖μ[(fun x => f x * g x) | m] ω‖ + ‖μ[f | m] ω * μ[g | m] ω‖ :=
      norm_sub_le _ _
    _ ≤ R * S + R * S := add_le_add hfgω (by
      rw [norm_mul]
      exact mul_le_mul hfω hgω (norm_nonneg _) hR)
    _ = 2 * R * S := by ring

theorem tendsto_integral_sq_sub_of_bounded_ae
    (μ : Measure Ω) [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ) (hY : AEStronglyMeasurable Y μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hbX : ∀ n, ∀ᵐ ω ∂μ, ‖X n ω‖ ≤ R)
    (hbY : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ R)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖(X n ω - Y ω) ^ 2‖ ≤ (2 * R) ^ 2 := by
    filter_upwards [hbX n, hbY] with ω hx hy
    have hdiff : ‖X n ω - Y ω‖ ≤ 2 * R := by
      calc
        ‖X n ω - Y ω‖ ≤ ‖X n ω‖ + ‖Y ω‖ := norm_sub_le _ _
        _ ≤ 2 * R := by linarith
    rw [norm_pow]
    nlinarith [norm_nonneg (X n ω - Y ω)]
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ : Ω => (2 * R) ^ 2)
    (fun n => ((hX n).sub hY).pow 2) (integrable_const _) hbound
    (hlim.mono (fun ω hω => by
      simpa using (hω.sub tendsto_const_nhds).pow 2))
  simpa using ht

theorem tendsto_integral_sq_sub_posteriorCovariance
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    {f g : Ω → ℝ} {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R) (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ S) :
    Tendsto (fun n => ∫ ω,
      (posteriorCovariance μ (F n) f g ω -
        posteriorCovariance μ (⨆ n, F n) f g ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  apply tendsto_integral_sq_sub_of_bounded_ae μ
    (fun n => ((stronglyMeasurable_posteriorCovariance μ (F n) f g).mono
      (F.le n)).aestronglyMeasurable)
    (((stronglyMeasurable_posteriorCovariance μ (⨆ n, F n) f g).mono
      (iSup_le fun n => F.le n)).aestronglyMeasurable)
    (show 0 ≤ 2 * R * S by positivity)
  · exact fun n => ae_norm_posteriorCovariance_le μ (F n) hR hS hf hg
  · exact ae_norm_posteriorCovariance_le μ (⨆ n, F n) hR hS hf hg
  · exact tendsto_ae_posteriorCovariance μ F f g

theorem tendsto_integral_prod_sq_sub_of_bounded_ae
    {T : Type*} [MeasurableSpace T]
    (ν : Measure T) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {X : ℕ → T × Ω → ℝ} {Y : T × Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    {R : ℝ} (hR : 0 ≤ R)
    (hbX : ∀ n, ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ, ‖X n (t, ω)‖ ≤ R)
    (hbY : ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ, ‖Y (t, ω)‖ ≤ R)
    (hlim : ∀ᵐ t ∂ν, ∀ᵐ ω ∂μ,
      Tendsto (fun n => X n (t, ω)) atTop (𝓝 (Y (t, ω)))) :
    Tendsto (fun n => ∫ p, (X n p - Y p) ^ 2 ∂ν.prod μ) atTop (𝓝 0) := by
  apply tendsto_integral_sq_sub_of_bounded_ae (ν.prod μ)
    (fun n => (hX n).aestronglyMeasurable) hY.aestronglyMeasurable hR
  · intro n
    exact (Measure.ae_prod_iff_ae_ae (measurableSet_le (hX n).norm measurable_const)).mpr (hbX n)
  · exact (Measure.ae_prod_iff_ae_ae (measurableSet_le hY.norm measurable_const)).mpr hbY
  · exact (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun hX hY)).mpr hlim

theorem tendsto_integral_prod_sq_sub_posteriorCovariance_versions
    {T : Type*} [MeasurableSpace T]
    (ν : Measure T) (μ : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (F : T → Filtration ℕ mΩ) {f g : Ω → ℝ} {R S : ℝ}
    (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R) (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ S)
    {X : ℕ → T × Ω → ℝ} {Y : T × Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hXversion : ∀ n, ∀ᵐ t ∂ν,
      (fun ω => X n (t, ω)) =ᵐ[μ] posteriorCovariance μ (F t n) f g)
    (hYversion : ∀ᵐ t ∂ν,
      (fun ω => Y (t, ω)) =ᵐ[μ] posteriorCovariance μ (⨆ n, F t n) f g) :
    Tendsto (fun n => ∫ p, (X n p - Y p) ^ 2 ∂ν.prod μ) atTop (𝓝 0) := by
  apply tendsto_integral_prod_sq_sub_of_bounded_ae ν μ hX hY
    (show 0 ≤ 2 * R * S by positivity)
  · intro n
    filter_upwards [hXversion n] with t ht
    filter_upwards [ht, ae_norm_posteriorCovariance_le μ (F t n) hR hS hf hg]
      with ω heq hbound
    rw [heq]
    exact hbound
  · filter_upwards [hYversion] with t ht
    filter_upwards [ht, ae_norm_posteriorCovariance_le μ (⨆ n, F t n) hR hS hf hg]
      with ω heq hbound
    rw [heq]
    exact hbound
  · filter_upwards [ae_all_iff.mpr hXversion, hYversion] with t hXt hYt
    filter_upwards [ae_all_iff.mpr hXt, hYt, tendsto_ae_posteriorCovariance μ (F t) f g]
      with ω hXω hYω hlim
    simpa only [hXω, hYω] using hlim

def observationExhaustionFiltration {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (X : Ω → ∀ i, E i)
    (hX : ∀ i, Measurable (fun ω => X ω i))
    (s : ℕ → Set ι) (hs : Monotone s) : Filtration ℕ mΩ where
  seq n := ⨆ i, ⨆ (_ : i ∈ s n), MeasurableSpace.comap (fun ω => X ω i) inferInstance
  mono' _ _ hnk := iSup₂_le fun i hi =>
    le_iSup_of_le i (le_iSup_of_le (hs hnk hi) le_rfl)
  le' _ := iSup₂_le fun i _ => (hX i).comap_le

theorem observationExhaustionFiltration_eq_comap {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (X : Ω → ∀ i, E i)
    (hX : ∀ i, Measurable (fun ω => X ω i))
    (s : ℕ → Set ι) (hs : Monotone s) (n : ℕ) :
    observationExhaustionFiltration X hX s hs n =
      MeasurableSpace.comap (fun ω (i : s n) => X ω i) inferInstance := by
  simp only [observationExhaustionFiltration, MeasurableSpace.comap_process_pi,
    iSup_subtype']

theorem observationExhaustionFiltration_iSup {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (X : Ω → ∀ i, E i)
    (hX : ∀ i, Measurable (fun ω => X ω i))
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n) :
    (⨆ n, observationExhaustionFiltration X hX s hs n) =
      MeasurableSpace.comap X inferInstance := by
  rw [MeasurableSpace.comap_process_pi (fun i ω => X ω i)]
  apply le_antisymm
  · exact iSup_le fun n => iSup₂_le fun i _ => le_iSup_of_le i le_rfl
  · apply iSup_le
    intro i
    obtain ⟨n, hn⟩ := hex i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hn le_rfl))

theorem tendsto_integral_sq_sub_observationCovariance
    {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ∀ i, E i) (hX : ∀ i, Measurable (fun ω => X ω i))
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f g : Ω → ℝ} {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ R) (hg : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ S) :
    Tendsto (fun n => ∫ ω,
      (posteriorCovariance μ
        (MeasurableSpace.comap (fun ω (i : s n) => X ω i) inferInstance) f g ω -
       posteriorCovariance μ (MeasurableSpace.comap X inferInstance) f g ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have h := tendsto_integral_sq_sub_posteriorCovariance μ
    (observationExhaustionFiltration X hX s hs) hR hS hf hg
  rw [observationExhaustionFiltration_iSup X hX s hs hex] at h
  simpa only [observationExhaustionFiltration_eq_comap] using h

end Problem367

end

end OAI
