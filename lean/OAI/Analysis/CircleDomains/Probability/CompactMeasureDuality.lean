import OAI.Analysis.CircleDomains.Probability.CompactMeasureDensity
import OAI.Analysis.CircleDomains.Probability.CompactFiniteMeasureBorel

namespace OAI

/-! The exact measure-image dual conclusion for a compact family avoiding
zero, including support in that family and the original squared-norm bound. -/
open Set Function Filter MeasureTheory
open scoped ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_measure_image_duality
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    (c : ℝ≥0) (hc : 0 < c)
    (hmod : (c : ℝ≥0∞) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ (η : ProbabilityMeasure (FiniteMeasure Z)) (q : Z → ℝ≥0∞),
      Measurable q ∧ (∀ᵐ v ∂(η : Measure (FiniteMeasure Z)), v ∈ S) ∧
      (∀ E, MeasurableSet E →
        (∫⁻ v, (v : Measure Z) E ∂(η : Measure (FiniteMeasure Z))) = σ.withDensity q E) ∧
      (∫⁻ z, q z^2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹ := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hcr : (0 : ℝ) < c := hc
  have hsqrt : 0 < Real.sqrt (c : ℝ) := Real.sqrt_pos.mpr hcr
  have hsq : (Real.sqrt (c : ℝ))^2 = c := Real.sq_sqrt c.coe_nonneg
  have hm : ENNReal.ofReal ((Real.sqrt (c : ℝ))^2) <
      measureFamilyModulus S Z σ (fun v => v.val) := by simpa only [hsq,ENNReal.ofReal_coe_nnreal] using hmod
  obtain ⟨P,q,hq,hbar,he⟩ :=
    exists_compact_measure_density_plan σ hS hne hz (Real.sqrt (c : ℝ)) hsqrt hm
  have hval : Measurable (fun v : S => v.val) := measurable_subtype_coe
  let η : ProbabilityMeasure (FiniteMeasure Z) := P.map (fun v : S => v.val)
  refine ⟨η,q,hq,?_,?_,?_⟩
  · change ∀ᵐ v ∂(P : Measure S).map (fun v : S => v.val), v ∈ S
    apply (ae_map_iff hval.aemeasurable (compact_finiteMeasure_measurableSet hS)).mpr
    exact Eventually.of_forall (fun v => v.property)
  · intro E hE
    change (∫⁻ v, (v : Measure Z) E ∂(P : Measure S).map (fun v : S => v.val)) = _
    have hev : Measurable (fun v : FiniteMeasure Z => (v : Measure Z) E) :=
      (Measure.measurable_coe hE).comp measurable_subtype_coe
    rw [lintegral_map hev hval]
    rw [← compactMeasureBarycenter_apply P hE,hbar]
  · refine he.trans_eq ?_
    rw [inv_pow,hsq,ENNReal.ofReal_inv_of_pos hcr,ENNReal.ofReal_coe_nnreal]

end CircleDomainRigidity

end

end OAI
