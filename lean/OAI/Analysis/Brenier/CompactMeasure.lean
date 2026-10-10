import OAI.Analysis.Brenier.Basic

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

section General

variable {X F : Type*} [TopologicalSpace X] [T2Space X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup F]
  {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} {f : X → F}

/-- Continuity only on a compact set of full measure suffices for integrability. -/
theorem integrable_of_continuousOn_of_ae_mem_compact
    (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) (hf : ContinuousOn f K) :
    Integrable f μ := by
  have h := hf.integrableOn_compact hK (μ := μ)
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h
  exact h

/-- The preceding result through a measurable pushforward. -/
theorem integrable_comp_of_continuousOn_of_map_ae_mem_compact
    {A : Type*} [MeasurableSpace A] {ρ : Measure A} [IsFiniteMeasure ρ]
    {T : A → X} (hT : Measurable T) (hK : IsCompact K)
    (hρ : ∀ᵐ x ∂Measure.map T ρ, x ∈ K) (hf : ContinuousOn f K) :
    Integrable (fun x => f (T x)) ρ := by
  exact (integrable_of_continuousOn_of_ae_mem_compact hK hρ hf).comp_measurable hT

end General

/-- Continuous-on-support functions are integrable for compactly supported finite measures. -/
theorem IsSupported.integrable_continuousOn
    {d : ℕ} {μ : Measure (E d)} [IsFiniteMeasure μ] {K : Set (E d)}
    (hμ : IsSupported μ K) (hK : IsCompact K)
    {F : Type*} [NormedAddCommGroup F] {f : E d → F} (hf : ContinuousOn f K) :
    Integrable f μ := by
  exact integrable_of_continuousOn_of_ae_mem_compact hK (ae_iff.mpr hμ) hf

/-- A continuous potential on a compact target is integrable after a measurable transport. -/
theorem integrable_comp_of_supported_map
    {d : ℕ} {A : Type*} [MeasurableSpace A] {ρ : Measure A} [IsFiniteMeasure ρ]
    {T : A → E d} (hT : Measurable T) {K : Set (E d)}
    (hK : IsCompact K) (hρ : IsSupported (Measure.map T ρ) K)
    {F : Type*} [NormedAddCommGroup F] {f : E d → F} (hf : ContinuousOn f K) :
    Integrable (fun x => f (T x)) ρ := by
  exact (hρ.integrable_continuousOn hK hf).comp_measurable hT

/-- Every continuous function on the compact product support of a coupling is integrable. -/
theorem IsCoupling.integrable_continuousOn_prod
    {d : ℕ} {μ ν : Measure (E d)} {π : Measure (E d × E d)}
    (hπ : IsCoupling μ ν π) {K Y : Set (E d)}
    (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y)
    {F : Type*} [NormedAddCommGroup F] {f : E d × E d → F}
    (hf : ContinuousOn f (K ×ˢ Y)) : Integrable f π := by
  let : IsProbabilityMeasure π := hπ.1
  have hfst : ∀ᵐ p ∂π, p.1 ∈ K := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hπ.2.1]
    exact ae_iff.mpr hμ
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Y := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact ae_iff.mpr hν
  apply integrable_of_continuousOn_of_ae_mem_compact (hK.prod hY) _ hf
  filter_upwards [hfst, hsnd] with p hpK hpY
  exact ⟨hpK, hpY⟩

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem358
namespace CompactIntegrability

variable {d : ℕ} {ρ : Measure (E d)} {T S : E d → E d}
  {Y Z : Set (E d)}

/-- A compact-supported pushforward puts the map in that compact set almost everywhere. -/
theorem ae_mem_of_supported_map (hT : Measurable T) (hY : IsCompact Y)
    (hTY : IsSupported (Measure.map T ρ) Y) : ∀ᵐ x ∂ρ, T x ∈ Y := by
  apply (ae_map_iff hT.aemeasurable hY.measurableSet).mp
  exact ae_iff.mpr hTY

/-- Every natural moment of the norm of a compact-valued measurable map is integrable. -/
theorem integrable_norm_pow_of_ae_mem [IsFiniteMeasure ρ]
    (hT : Measurable T) (hY : IsCompact Y) (hTY : ∀ᵐ x ∂ρ, T x ∈ Y)
    (n : ℕ) : Integrable (fun x => ‖T x‖ ^ n) ρ := by
  obtain ⟨R, hRpos, hR⟩ := hY.isBounded.exists_pos_norm_le
  apply (integrable_const (R ^ n)).mono' (hT.norm.pow_const n).aestronglyMeasurable
  filter_upwards [hTY] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hR _ hx) n

/-- Squared norm integrability from compact support of the pushforward. -/
theorem integrable_norm_sq_of_supported_map [IsFiniteMeasure ρ]
    (hT : Measurable T) (hY : IsCompact Y)
    (hTY : IsSupported (Measure.map T ρ) Y) :
    Integrable (fun x => ‖T x‖ ^ 2) ρ :=
  integrable_norm_pow_of_ae_mem hT hY (ae_mem_of_supported_map hT hY hTY) 2

/-- An almost-everywhere limit of maps into a fixed compact set stays in that set. -/
theorem ae_mem_of_ae_tendsto {F : ℕ → E d → E d}
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x))) :
    ∀ᵐ x ∂ρ, T x ∈ Y := by
  have hmem : ∀ᵐ x ∂ρ, ∀ n, F n x ∈ Y := ae_all_iff.mpr hFY
  filter_upwards [hmem, hlim] with x hx hlimx
  exact hY.isClosed.mem_of_tendsto hlimx (Filter.Eventually.of_forall hx)

/-- Compact range supplies the domination needed to pass to continuous test integrals. -/
theorem tendsto_integral_comp_of_ae_tendsto [IsFiniteMeasure ρ]
    {F : ℕ → E d → E d} (hF : ∀ n, Measurable (F n))
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x)))
    {φ : E d → ℝ} (hφ : Continuous φ) :
    Filter.Tendsto (fun n => ∫ x, φ (F n x) ∂ρ) Filter.atTop
      (𝓝 (∫ x, φ (T x) ∂ρ)) := by
  obtain ⟨R, _, hR⟩ := (hY.image hφ).isBounded.exists_pos_norm_le
  apply tendsto_integral_of_dominated_convergence (fun _ => R)
  · intro n
    exact (hφ.measurable.comp (hF n)).aestronglyMeasurable
  · exact integrable_const R
  · intro n
    filter_upwards [hFY n] with x hx
    exact hR _ ⟨F n x, hx, rfl⟩
  · filter_upwards [hlim] with x hx
    exact hφ.continuousAt.tendsto.comp hx

/-- Almost-everywhere convergence within a common compact range implies convergence of
squared map distances. This is the bounded-convergence step in finite-target approximation. -/
theorem tendsto_integral_sub_norm_sq_of_ae_tendsto [IsFiniteMeasure ρ]
    {F : ℕ → E d → E d} (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x))) :
    Filter.Tendsto (fun n => ∫ x, ‖F n x - T x‖ ^ 2 ∂ρ) Filter.atTop (𝓝 0) := by
  have hTY := ae_mem_of_ae_tendsto hY hFY hlim
  obtain ⟨R, hRpos, hR⟩ := hY.isBounded.exists_pos_norm_le
  have hdom := tendsto_integral_of_dominated_convergence (μ := ρ)
    (F := fun n x => ‖F n x - T x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * R) ^ 2)
  apply (by simpa using hdom : _)
  · intro n
    exact ((hF n).sub hT).norm.pow_const 2 |>.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hFY n, hTY] with x hx hxT
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    calc
      ‖F n x - T x‖ ≤ ‖F n x‖ + ‖T x‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hR _ hx) (hR _ hxT)
      _ = 2 * R := by ring
  · filter_upwards [hlim] with x hx
    have hc : Tendsto (fun _ : ℕ => T x) atTop (𝓝 (T x)) := tendsto_const_nhds
    simpa using (hx.sub hc).norm.pow 2

/-- Compact-range bounded convergence stated using the problem's exact map distance. -/
theorem tendsto_mapL2Dist_of_ae_tendsto [IsFiniteMeasure ρ]
    {F : ℕ → E d → E d} (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (T x))) :
    Filter.Tendsto (fun n => mapL2Dist ρ (F n) T) Filter.atTop (𝓝 0) := by
  have h := tendsto_integral_sub_norm_sq_of_ae_tendsto hF hT hY hFY hlim
  simpa [mapL2Dist, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h

end CompactIntegrability

namespace CompactIntegrability

variable {d : ℕ} {ρ μ : Measure (E d)} {Y : Set (E d)}
  {F Q : ℕ → E d → E d} {T : E d → E d}

/-- Identify a compact-range pointwise limit's law by continuous test integrals. -/
theorem map_eq_of_ae_tendsto_of_test_tendsto [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hY : IsCompact Y) (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => F n x) atTop (𝓝 (T x)))
    (htest : ∀ φ : E d → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ (F n x) ∂ρ) atTop (𝓝 (∫ y, φ y ∂μ))) :
    Measure.map T ρ = μ := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  have hφ : Continuous (φ : E d → ℝ) := map_continuous φ
  rw [integral_map hT.aemeasurable hφ.measurable.aestronglyMeasurable]
  exact tendsto_nhds_unique
    (tendsto_integral_comp_of_ae_tendsto hF hY hFY hlim hφ) (htest φ hφ)

/-- If the approximating maps have the laws of quantizers converging to the identity,
the almost-everywhere limit has the original target law. -/
theorem map_eq_of_ae_tendsto_of_map_eq_quantizers [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    (hF : ∀ n, Measurable (F n)) (hT : Measurable T)
    (hQ : ∀ n, Measurable (Q n)) (hY : IsCompact Y)
    (hFY : ∀ n, ∀ᵐ x ∂ρ, F n x ∈ Y)
    (hQY : ∀ n, ∀ᵐ y ∂μ, Q n y ∈ Y)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => F n x) atTop (𝓝 (T x)))
    (hQlim : ∀ᵐ y ∂μ, Tendsto (fun n => Q n y) atTop (𝓝 y))
    (hpush : ∀ n, Measure.map (F n) ρ = Measure.map (Q n) μ) :
    Measure.map T ρ = μ := by
  apply map_eq_of_ae_tendsto_of_test_tendsto hF hT hY hFY hlim
  intro φ hφ
  have htest := tendsto_integral_comp_of_ae_tendsto hQ hY hQY hQlim hφ
  have heq : (fun n => ∫ x, φ (F n x) ∂ρ) = (fun n => ∫ y, φ (Q n y) ∂μ) := by
    funext n
    rw [← integral_map (hF n).aemeasurable hφ.measurable.aestronglyMeasurable,
      hpush n, integral_map (hQ n).aemeasurable hφ.measurable.aestronglyMeasurable]
  rw [heq]
  exact htest

end CompactIntegrability
end Problem358

end

end OAI
