import OAI.Probability.SLE.Geometry.NormalizedRestartGoodSet
import OAI.Probability.SLE.Mass.PositiveMassContinuity

namespace OAI

/-! Random normalization commutes with the raw mass process on one event
  for every finite horizon. Future-dependent horizons may then be used. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge.Multipoint
local instance normalizedAllTimesMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance normalizedAllTimesBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance normalizedAllTimesLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)
  (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
  (F : Ω → ℝ≥0 → ℂ → ℂ)
  (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
  (R : RawCanonicalMass)
  (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
    R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
  (E : Set C(ℝ≥0,ℝ)) (hE : MeasurableSet E)
  (hEf : ∀ᵐ p ∂P.map (sourceDriverPath B hc), p∈E)
  (hEp : ∀ p∈E, PositiveMassPaths (fun t => R.process t p) (R.terminal p))
  (τ : Ω → ℝ≥0)
  (hτ : IsStoppingTime (Filtration.natural B (fun s =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
    (fun ω => (τ ω:WithTop ℝ≥0)))
  (a : Ω → ℝ≥0) (haM : Measurable[hτ.measurableSpace] a) (ha : ∀ ω, 0<a ω)

include C hB hc F hw R he E hE hEf hEp τ hτ a haM ha in
theorem CanonicalMass.normalized_raw_scaling_all_times :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      dilationMass κ (a ω) (ha ω) (R.process t
        (scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω))) =
      R.process ((a ω)^2*t) (sourceRestartDriverPath B hc τ ω) := by
  let Y := fun ω => scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω)
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.of_uncurry_left
  have hYm : Measurable Y := measurable_scaleDriverPath.comp
    ((haM.mono hτ.measurableSpace_le le_rfl).inv.prodMk
      (sourceRestartDriverPath_measurable B hm hc τ hτ))
  have hYlaw := source_restart_random_scale_driver_law B hB hm hc τ hτ
    (fun ω => (a ω)⁻¹) haM.inv (fun ω => inv_pos.mpr (ha ω))
  let L := fun t ω => dilationMass κ (a ω) (ha ω) (R.process t (Y ω))
  let N := fun t ω => R.process ((a ω)^2*t) (sourceRestartDriverPath B hc τ ω)
  have hdense (j : ℕ) : ∀ᵐ ω ∂P, L (TopologicalSpace.denseSeq ℝ≥0 j) ω=N (TopologicalSpace.denseSeq ℝ≥0 j) ω := by
    filter_upwards [C.random_raw_scaled_mass_eq hB hc F hw R he E hE hEf hEp
      hτ.measurableSpace hτ.measurableSpace_le Y hYm hYlaw a
      (fun _ => TopologicalSpace.denseSeq ℝ≥0 j) haM measurable_const ha] with ω hω
    simpa only [L,N,Y,scaleDriverPath_inv_cancel (a ω) (ha ω)] using hω
  have hYgood := normalized_restart_mem_full_driver_set hB hm hc τ hτ a haM ha E hE hEf
  have hNgood := sourceRestart_mem_full_driver_set hB hm hc τ hτ E hE hEf
  apply random_radon_process_eq_of_positive_tests P (localTestFamily upperHalfPlane) L N
  · intro t ω
    let := (R.radon t (Y ω)).2
    exact (conformalMass_radon _ _ _).1
  · intro t ω
    exact (R.radon _ _).1
  · intro f _hf
    filter_upwards [ae_all_iff.mpr hdense,hYgood,hNgood] with ω hω hYω hNω
    have hpY := hEp _ hYω
    have hpN := hEp _ hNω
    have hL : Continuous (fun t => ∫ z,f z ∂L t ω) :=
      conformalMass_test_continuous _ _ _ hpY.continuous_real_tests f
    have hN : Continuous (fun t => ∫ z,f z ∂N t ω) :=
      (hpN.continuous_real_tests f).comp (continuous_const.mul continuous_id)
    have heq := (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer hL hN
      (by funext j; simp only [Function.comp_apply]; rw [hω j])
    intro t
    exact congrFun heq t

include C hB hc F hw R he E hE hEf hEp τ hτ a haM ha in
theorem CanonicalMass.normalized_raw_restart_all_times (hκ : 0<κ)
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, C.process (τ ω+(a ω)^2*t) ω-C.process (τ ω) ω =
      weightedImageMass (stoppedMassPoint B κ γ G F hw τ ω) (stoppedMassWeight B κ F τ ω)
        (dilationMass κ (a ω) (ha ω) (R.process t
          (scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω)))) := by
  filter_upwards [C.normalized_raw_scaling_all_times hB hc F hw R he E hE hEf hEp τ hτ a haM ha,
    C.raw_fixed_restart hB hc hκ F hw R he E hE hEf hEp hpublished τ hτ] with ω hs hr
  intro t
  rw [hr ((a ω)^2*t)]
  change weightedImageMass _ _ (R.process ((a ω)^2*t) (sourceRestartDriverPath B hc τ ω))=_
  rw [hs t]

end SLEExactGauge.Multipoint

end

end OAI
