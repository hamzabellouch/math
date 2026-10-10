import OAI.Probability.SLE.Geometry.NormalizedRawAllTimes
import OAI.Probability.SLE.Geometry.RestartCellBounds

namespace OAI

/-! Canonical physical cell mass versus the same raw normalized disk mass,
simultaneously at every finite horizon, including a future random one. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint
local instance normalizedCellAllTimesMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance normalizedCellAllTimesBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma CanonicalMass.normalized_cell_bounds_all_times
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ)
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
    (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
    (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (a : Ω → ℝ≥0) (haM : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0 < a ω) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) Real.pi)
      (z : ℂ) (_hz : z ∈ survivingDomain (γ ω) (τ ω))
      (r : ℝ) (_hr : 0 < r)
      (_hR : fullRadius (G ω) (τ ω) z=(2048*Real.pi)*r)
      (_hpolar : G ω (τ ω) z=(Real.sqrt κ*B (τ ω) ω:ℝ)+
        (a ω:ℂ)*Complex.exp (θ*Complex.I)),
      let L := ENNReal.ofReal (compactWeightedMass (Target.diskMassWeight κ θ hθ)
        (Target.diskSourceHalfPlane θ)
        (R.process T (scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω))))
      ENNReal.ofReal (((128*Real.pi)*r)^dimension κ)*L ≤
          C.process (τ ω+(a ω)^2*T) ω
            (Subtype.val ⁻¹' closedBall z ((4096*Real.pi)*r)) ∧
        ∀ A : Set ℂ, MeasurableSet A → A ⊆ closedBall z (2*r) →
          A ⊆ survivingDomain (γ ω) (τ ω) →
          C.process (τ ω+(a ω)^2*T) ω (Subtype.val ⁻¹' A) ≤
            ENNReal.ofReal (((32768*Real.pi)*r)^dimension κ)*L := by
  filter_upwards [C.paths,C.normalized_raw_restart_all_times hB hc F hw R he E hE hEf hEp
    τ hτ a haM ha hκ hpublished] with ω hp hrst
  intro T θ hθ z hz r hr hR hpolar
  let := (C.radon (τ ω) ω).2
  let := (R.radon T (scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω))).2
  exact (hw ω).restarted_cell_mass_bounds hgrowth κ hκ (τ ω) (τ ω+(a ω)^2*T)
    (le_add_of_nonneg_right (by positivity)) (fun t => C.process t ω) hp.monotone
    (fun A hA => hp.zero_on_surviving_subset (τ ω) A hA) θ hθ (a ω) (ha ω)
    (R.process T (scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω)))
    (hrst T) z hz hpolar r hr hR

end SLEExactGauge.Multipoint

end

end OAI
