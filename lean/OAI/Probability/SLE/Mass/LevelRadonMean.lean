import OAI.Probability.SLE.Mass.ConvexMeanMeasure
import OAI.Probability.SLE.Mass.LevelRadonMoments
import OAI.Probability.SLE.Mass.RadonTestDetermines

namespace OAI

/-! The actual terminal Radon limit has exactly the initial Green mean
measure. Local moment bounds justify signed compact tests of that mean. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem level_radon_terminal_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (ν : Ω → Measure upperHalfPlane) (hνm : Measurable ν)
    (hν : ∀ ω, (ν ω).Regular)
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n ∞ ω)
        atTop (𝓝 (∫ z, f z ∂ν ω)))
    (hmeanlim : ∀ k, Tendsto (fun n => ∫ ω, (∫ z, (localTestFamily upperHalfPlane).test k z
        ∂convexLevelMeasure κ B γ G u s w n ∞ ω) ∂P)
      atTop (𝓝 (∫ ω, (∫ z, (localTestFamily upperHalfPlane).test k z ∂ν ω) ∂P))) :
    P.bind ν = initialGreenMeasure κ := by
  let (ω : Ω) : (ν ω).Regular := hν ω
  let : IsFiniteMeasureOnCompacts (P.bind ν) := by
    constructor
    intro K hK
    rw [Measure.bind_apply hK.measurableSet hνm.aemeasurable]
    simpa only [pow_one] using level_radon_limit_compact_moments hB hm hBm hBc hB0 hκ hκ8
      γ G F hw hgrowth u hu s w hw₀ hw₁ ∞ ν (fun _ => inferInstance) hlim K hK 1
  let := initialGreenMeasure_finite_on_compacts κ
  apply (localTestFamily upperHalfPlane).measure_eq_of_test_integrals
  intro k
  let f := (localTestFamily upperHalfPlane).test k
  have hmconst (n : ℕ) : (∫ ω, (∫ z, f z ∂convexLevelMeasure κ B γ G u s w n ∞ ω) ∂P) =
      ∫ z, f z ∂initialGreenMeasure κ :=
    (convexLevelMeasure_terminal_test_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw u hu s w hw₀ hw₁ n f).2
  have he : (∫ ω, (∫ z, f z ∂ν ω) ∂P) = ∫ z, f z ∂initialGreenMeasure κ := by
    apply tendsto_nhds_unique (hmeanlim k)
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun n => (hmconst n).symm)
  rw [← he]
  exact (integral_bind_of_integrable_sections P ν hνm f f.continuous.measurable
    (fun _ => f.integrable) f.integrable).symm

end SLEExactGauge.Multipoint

end

end OAI
