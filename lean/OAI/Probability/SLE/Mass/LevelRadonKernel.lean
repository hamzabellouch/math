import OAI.Probability.SLE.Mass.ConvexCurrentMean
import OAI.Probability.SLE.Mass.LevelRadonMoments
import OAI.Probability.SLE.Mass.RadonTestDetermines

namespace OAI

/-! Passage of the conditional Green kernel to the actual common Radon
limits. The hypotheses on the limits are exactly those furnished by the
common convex extraction, including its retained L² pairings. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma level_radon_mean_finite_on_compacts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane) (hνm : Measurable ν)
    (hν : ∀ ω, IsFiniteMeasureOnCompacts (ν ω))
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω))) (E : Set Ω) :
    IsFiniteMeasureOnCompacts ((P.restrict E).bind ν) := by
  constructor
  intro K hK
  rw [Measure.bind_apply hK.measurableSet hνm.aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self (le_refl _))
  simpa only [pow_one] using level_radon_limit_compact_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth u hu s w hw₀ hw₁ t ν hν hlim K hK 1

theorem level_radon_conditional_kernel
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hmono : Monotone u) (huLim : Tendsto u atTop atTop)
    (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0) (ν : Fin 2 → Ω → Measure upperHalfPlane)
    (hνm : ∀ j, Measurable (ν j))
    (hν : ∀ j ω, (ν j ω).Regular ∧ IsFiniteMeasureOnCompacts (ν j ω))
    (hlim : ∀ j, ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n
        (if j = 0 then (t : ℝ≥0∞) else ∞) ω) atTop (𝓝 (∫ z, f z ∂ν j ω)))
    (hpair : ∀ j k (a : Ω → ℝ), MemLp a 2 P →
      Tendsto (fun n => ∫ ω, a ω * (∫ z, (localTestFamily upperHalfPlane).test k z
        ∂convexLevelMeasure κ B γ G u s w n (if j = 0 then (t : ℝ≥0∞) else ∞) ω) ∂P)
        atTop (𝓝 (∫ ω, a ω * (∫ z, (localTestFamily upperHalfPlane).test k z ∂ν j ω) ∂P)))
    (E : Set Ω)
    (hE : MeasurableSet[Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable) t] E) :
    (P.restrict E).bind (ν 1) = (P.restrict E).bind (ν 0) +
      (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let τ (j : Fin 2) : ℝ≥0∞ := if j = 0 then t else ∞
  let (j : Fin 2) (ω : Ω) : IsFiniteMeasureOnCompacts (ν j ω) := (hν j ω).2
  let (j : Fin 2) : IsFiniteMeasureOnCompacts ((P.restrict E).bind (ν j)) :=
    level_radon_mean_finite_on_compacts hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      u hu s w hw₀ hw₁ (τ j) (ν j) (hνm j) (fun _ => inferInstance) (hlim j) E
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hgreen := halfPlaneGreenMeasure_mean_le hB hBm hBc hB0 hκ hκ8 γ G F hw t E
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t)) :=
    ⟨fun K hK => lt_of_le_of_lt (hgreen K) hK.measure_lt_top⟩
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind (ν 0) +
      (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G t)) := by
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩
  have hEg : MeasurableSet E := (Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)).le t E hE
  apply (localTestFamily upperHalfPlane).measure_eq_of_test_integrals
  intro k
  let f := (localTestFamily upperHalfPlane).test k
  have hc (j : Fin 2) : Tendsto (fun n => ∫ z, f z
      ∂(P.restrict E).bind (convexLevelMeasure κ B γ G u s w n (τ j))) atTop
      (𝓝 (∫ z, f z ∂(P.restrict E).bind (ν j))) := by
    apply mean_test_tendsto_of_L2_pairings P _ (ν j)
      (fun n => convexLevelMeasure_measurable hm hBc κ γ G F hw u hu s w n (τ j))
      (hνm j) f f.continuous.measurable
    · intro n ω
      let := convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w n (τ j)
      exact f.integrable
    · exact fun _ => f.integrable
    · exact hEg
    · intro n
      exact f.integrable.mono_measure (convexLevelMeasure_mean_le hB hBm hBc hB0 hκ hκ8
        γ G F hw u hu s w hw₀ hw₁ n (τ j) E)
    · exact f.integrable
    · exact hpair j k
  have ht := hc 0
  have hi := hc 1
  have hg := convexCurrentMean_test_tendsto hB hBm hBc hB0 hκ hκ8 γ G F hw
    u hu hmono huLim s w hw₀ hw₁ t E f
  simp [τ] at ht hi
  have he (n : ℕ) : (∫ z, f z ∂(P.restrict E).bind (convexLevelMeasure κ B γ G u s w n ∞)) =
      (∫ z, f z ∂(P.restrict E).bind (convexLevelMeasure κ B γ G u s w n t)) +
        ∫ z, f z ∂convexCurrentMean (P.restrict E) κ B γ G u s w n t := by
    rw [convexLevelMeasure_conditional_split hB hBm hBc hB0 hκ hκ8 γ G F hw u hu s w n t E hE]
    exact integral_add_measure
      (f.integrable.mono_measure (convexLevelMeasure_mean_le hB hBm hBc hB0 hκ hκ8
        γ G F hw u hu s w hw₀ hw₁ n t E))
      (f.integrable.mono_measure (convexCurrentMean_le hB hBm hBc hB0 hκ hκ8
        γ G F hw u hu s w hw₀ hw₁ n t E))
  rw [integral_add_measure f.integrable f.integrable]
  apply tendsto_nhds_unique hi
  exact (ht.add hg).congr' (Eventually.of_forall (fun n => (he n).symm))

end SLEExactGauge.Multipoint

end

end OAI
