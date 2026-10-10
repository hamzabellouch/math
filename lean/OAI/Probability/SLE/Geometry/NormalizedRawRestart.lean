import OAI.Probability.SLE.Loewner.RawFixedRestart
import OAI.Probability.SLE.Geometry.RandomRawScaleTests

namespace OAI

/-! The same raw canonical functional after a finite stopping time and a
positive normalization scale chosen from the stopped past. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma scaleDriverPath_inv_cancel (c : ℝ≥0) (hc : 0 < c) (p : C(ℝ≥0,ℝ)) :
    scaleDriverPath c (scaleDriverPath c⁻¹ p)=p := by
  ext t
  change (c:ℝ)*(((c⁻¹:ℝ≥0):ℝ)*p (t/c^2/(c⁻¹)^2))=p t
  rw [← mul_assoc]
  rw [show t/c^2/(c⁻¹)^2=t by field_simp [hc.ne']]
  rw [NNReal.coe_inv,mul_inv_cancel₀ (show (c:ℝ)≠0 from ne_of_gt hc),one_mul]

namespace Multipoint
local instance normalizedRawRestartMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance normalizedRawRestartBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

lemma CanonicalMass.normalized_raw_restart
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
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable))
      (fun ω => (τ ω:WithTop ℝ≥0)))
    (a T : Ω → ℝ≥0) (haM : Measurable[hτ.measurableSpace] a)
    (hT : Measurable[hτ.measurableSpace] T) (ha : ∀ ω, 0 < a ω) :
    ∀ᵐ ω ∂P, C.process (τ ω+(a ω)^2*T ω) ω-C.process (τ ω) ω =
      weightedImageMass (stoppedMassPoint B κ γ G F hw τ ω) (stoppedMassWeight B κ F τ ω)
        (dilationMass κ (a ω) (ha ω) (R.process (T ω)
          (scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω)))) := by
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  let Y : Ω → C(ℝ≥0,ℝ) := fun ω =>
    scaleDriverPath (a ω)⁻¹ (sourceRestartDriverPath B hc τ ω)
  have hYm : Measurable Y := measurable_scaleDriverPath.comp
    ((haM.mono hτ.measurableSpace_le le_rfl).inv.prodMk
      (sourceRestartDriverPath_measurable B hm hc τ hτ))
  have hYlaw := source_restart_random_scale_driver_law B hB hm hc τ hτ
    (fun ω => (a ω)⁻¹) haM.inv (fun ω => inv_pos.mpr (ha ω))
  have hs := C.random_raw_scaled_mass_eq hB hc F hw R he E hE hEf hEp
    hτ.measurableSpace hτ.measurableSpace_le Y hYm hYlaw a T haM hT ha
  filter_upwards [C.raw_fixed_restart hB hc hκ F hw R he E hE hEf hEp hpublished τ hτ,hs]
    with ω hr hsω
  rw [hr ((a ω)^2*T ω)]
  change weightedImageMass _ _ (R.process ((a ω)^2*T ω) (sourceRestartDriverPath B hc τ ω))=_
  rw [hsω]
  simp only [Y,scaleDriverPath_inv_cancel (a ω) (ha ω)]

end Multipoint
end SLEExactGauge

end

end OAI
