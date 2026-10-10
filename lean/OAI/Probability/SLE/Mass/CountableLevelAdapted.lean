import OAI.Probability.SLE.Mass.LevelApproximationAdapted

namespace OAI

/-! A common family of actual convex limits admits simultaneous versions
measurable in the original natural past at each prescribed finite time. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge.Multipoint

theorem countable_level_limits_have_past_versions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (t : ℕ → ℝ≥0)
    (ν : ℕ → Ω → Measure upperHalfPlane)
    (hν : ∀ᵐ ω ∂P, ∀ j, (ν j ω).Regular)
    (hlim : ∀ᵐ ω ∂P, ∀ j (f : C_c(upperHalfPlane,ℝ)),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
        atTop (𝓝 (∫ z, f z ∂ν j ω))) :
    ∃ η : ℕ → Ω → Measure upperHalfPlane,
      (∀ j, Measurable[Filtration.natural B (fun r => (hm r).stronglyMeasurable) (t j)] (η j)) ∧
      (∀ j ω, (η j ω).Regular ∧ IsFiniteMeasureOnCompacts (η j ω)) ∧
      ∀ᵐ ω ∂P, ∀ j, η j ω = ν j ω := by
  have hex (j : ℕ) : ∃ η : Ω → Measure upperHalfPlane,
      Measurable[Filtration.natural B (fun r => (hm r).stronglyMeasurable) (t j)] η ∧
      (∀ ω, (η ω).Regular ∧ IsFiniteMeasureOnCompacts (η ω)) ∧ η =ᵐ[P] ν j := by
    apply level_radon_limit_has_past_measurable_version P hm hc hκ hκ8 γ G F hw
      u hu s w hw₀ (t j) (ν j)
    · filter_upwards [hν] with ω hω
      exact hω j
    · filter_upwards [hlim] with ω hω
      exact hω j
  choose η hηm hηr hηeq using hex
  exact ⟨η,hηm,hηr,ae_all_iff.mpr hηeq⟩

end SLEExactGauge.Multipoint

end

end OAI
