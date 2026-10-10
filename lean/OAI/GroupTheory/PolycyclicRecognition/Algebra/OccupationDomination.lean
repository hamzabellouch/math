import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling

namespace OAI

/-! # Domination of translated chart samples by one occupation law -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The density comparison is made before projecting the coordinates. A
measure-preserving coordinate move therefore retains the same bound after
pushforward, without any injectivity requirement on the chart. -/
theorem map_densityProbabilityMeasure_le
    {D : Type*} [MeasurableSpace D] (m : Measure D)
    (η ρ : D → ℝ) (hiη : Integrable η m) (hiρ : Integrable ρ m)
    (hpη : ∀ z, 0 ≤ η z) (hpρ : ∀ z, 0 ≤ ρ z)
    (hmη : ∫ z, η z ∂m = 1) (hmρ : ∫ z, ρ z ∂m = 1)
    (hρ : Measurable ρ) (T : D → D) (hT : MeasurePreserving T m m)
    (c : ℝ≥0) (hbound : ∀ z, η z ≤ (c : ℝ) * ρ (T z)) :
    Measure.map T (densityProbabilityMeasure m η hiη hpη hmη : Measure D) ≤
      c • (densityProbabilityMeasure m ρ hiρ hpρ hmρ : Measure D) := by
  apply Measure.le_iff.mpr
  intro s hs
  change Measure.map T (m.withDensity (fun z => ENNReal.ofReal (η z))) s ≤
    (c • m.withDensity (fun z => ENNReal.ofReal (ρ z))) s
  rw [Measure.map_apply hT.measurable hs, Measure.smul_apply,
    withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs]
  calc
    _ ≤ ∫⁻ z in T ⁻¹' s, (c : ℝ≥0∞) * ENNReal.ofReal (ρ (T z)) ∂m := by
      apply lintegral_mono
      intro z
      simpa only [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal (hbound z)
    _ = (c : ℝ≥0∞) * ∫⁻ z in T ⁻¹' s, ENNReal.ofReal (ρ (T z)) ∂m :=
      lintegral_const_mul _ ((hρ.comp hT.measurable).ennreal_ofReal)
    _ = _ := by rw [hT.setLIntegral_comp_preimage hs hρ.ennreal_ofReal]; rfl

/-- A uniform upper bound on the initial density and a positive lower bound
on the swept support give the coordinate density comparison. -/
theorem density_bound_on_swept_support
    {D : Type*} (η ρ : D → ℝ) (T : D → D) (K : Set D)
    {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b)
    (hη : ∀ z, η z ≤ A) (hρ : ∀ z, 0 ≤ ρ z)
    (hsupp : ∀ z, η z ≠ 0 → T z ∈ K) (hlower : ∀ z ∈ K, b ≤ ρ z) :
    ∀ z, η z ≤ (A / b) * ρ (T z) := by
  intro z
  by_cases hz : η z = 0
  · rw [hz]
    exact mul_nonneg (div_nonneg hA hb.le) (hρ _)
  · calc
      η z ≤ A := hη z
      _ = (A / b) * b := (div_mul_cancel₀ A hb.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower _ (hsupp z hz)) (div_nonneg hA hb.le)

/-- Domination in the second sampling coordinate passes through the actual
chart and its exact action identity. -/
theorem map_productOccupationLaw_le
    {A D X : Type*} [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (σ ν : ProbabilityMeasure D)
    (p : A × D → X) (hp : Measurable p)
    (T : D → D) (hT : Measurable T) (act : X → X) (hact : Measurable act)
    (hmove : ∀ a z, act (p (a, z)) = p (a, T z))
    (c : ℝ≥0) (hdom : Measure.map T (σ : Measure D) ≤ c • (ν : Measure D)) :
    Measure.map act (productOccupationLaw μ σ p : Measure X) ≤
      c • (productOccupationLaw μ ν p : Measure X) := by
  change Measure.map act (Measure.map p ((μ : Measure A).prod (σ : Measure D))) ≤
    c • Measure.map p ((μ : Measure A).prod (ν : Measure D))
  have heq : act ∘ p = p ∘ Prod.map id T := by
    funext z
    exact hmove z.1 z.2
  rw [Measure.map_map hact hp, heq,
    ← Measure.map_map hp (measurable_id.prodMap hT),
    ← Measure.map_prod_map (μ : Measure A) (σ : Measure D) measurable_id hT,
    Measure.map_id]
  have h := Measure.map_mono (Measure.prod_mono (le_refl (μ : Measure A)) hdom) hp
  rw [Measure.prod_smul_right, Measure.map_smul] at h
  · exact h
  · exact hp.aemeasurable

end PolycyclicRecognition

end

end OAI
