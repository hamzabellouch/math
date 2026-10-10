import OAI.Probability.SLE.Geometry.WeightedCompactTerminal
import OAI.Probability.SLE.Geometry.PositiveKernelTests

namespace OAI

/-! Compact weighted tests of a positive kernel dominated in mean by the
initial Green measure. This also treats exceptional nonintegrable sections. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

lemma compactWeightedMass_kernel_lintegral_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hbound : P.bind μ ≤ initialGreenMeasure κ)
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K) :
    (∫⁻ ω, ∫⁻ z in K, (w z:ℝ≥0∞) ∂μ ω ∂P) ≠ ∞ := by
  let f : upperHalfPlane → ℝ := K.indicator (fun z => (w z:ℝ))
  have hfm : Measurable f :=
    (continuous_subtype_val.comp w.continuous).measurable.indicator hK.measurableSet
  have he (z : upperHalfPlane) : ENNReal.ofReal (f z)=K.indicator (fun z => (w z:ℝ≥0∞)) z := by
    by_cases hz : z ∈ K <;> simp [f,hz]
  have hfi : Integrable f (P.bind μ) := by
    let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
    exact ((integrable_indicator_iff hK.measurableSet).mpr
      (compact_weight_integrable w K hK (initialGreenMeasure κ))).mono_measure hbound
  simp_rw [← lintegral_indicator hK.measurableSet,← he]
  rw [← Measure.lintegral_bind (m := P) hμ.aemeasurable hfm.ennreal_ofReal.aemeasurable]
  exact (lintegral_ofReal_lt_top_of_integrable hfi).ne

lemma compactWeightedMass_kernel_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hbound : P.bind μ ≤ initialGreenMeasure κ)
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K) :
    Integrable (fun ω => compactWeightedMass w K (μ ω)) P ∧
      (∫ ω, compactWeightedMass w K (μ ω) ∂P) =
        compactWeightedMass w K (P.bind μ) := by
  let f : upperHalfPlane → ℝ := K.indicator (fun z => (w z:ℝ))
  have hfm : Measurable f :=
    (continuous_subtype_val.comp w.continuous).measurable.indicator hK.measurableSet
  have hf0 (z : upperHalfPlane) : 0 ≤ f z := by
    exact indicator_nonneg (fun z _ => (w z).coe_nonneg) z
  have hfi : Integrable f (P.bind μ) := by
    let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
    exact ((integrable_indicator_iff hK.measurableSet).mpr
      (compact_weight_integrable w K hK (initialGreenMeasure κ))).mono_measure hbound
  have hm : Measurable (fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂μ ω) :=
    (Measure.measurable_lintegral hfm.ennreal_ofReal).comp hμ
  have hfin : (∫⁻ ω, ∫⁻ z, ENNReal.ofReal (f z) ∂μ ω ∂P) ≠ ∞ := by
    rw [← Measure.lintegral_bind (m := P) hμ.aemeasurable hfm.ennreal_ofReal.aemeasurable,
      ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0)]
    exact ENNReal.ofReal_ne_top
  have he (ν : Measure upperHalfPlane) : compactWeightedMass w K ν =
      (∫⁻ z, ENNReal.ofReal (f z) ∂ν).toReal := by
    rw [compactWeightedMass,← integral_indicator hK.measurableSet]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable
  refine ⟨?_,?_⟩
  · simpa only [he] using integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin
  · simp_rw [he]
    rw [integral_toReal hm.aemeasurable (ae_lt_top hm hfin),
      ← Measure.lintegral_bind (m := P) hμ.aemeasurable hfm.ennreal_ofReal.aemeasurable]

end SLEExactGauge.Multipoint

end

end OAI
