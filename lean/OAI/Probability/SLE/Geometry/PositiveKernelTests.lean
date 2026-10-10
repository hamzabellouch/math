import OAI.Probability.SLE.Mass.CanonicalMassUniqueness

namespace OAI

/-! Positive compact tests of random measures whose mean is bounded by
the initial Green measure. Exceptional infinite values need no modification. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance positiveKernelTestsLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

lemma positive_kernel_test_lintegral_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hbound : P.bind μ ≤ initialGreenMeasure κ)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    (∫⁻ ω, ∫⁻ z, ENNReal.ofReal (f z) ∂μ ω ∂P) ≠ ∞ := by
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hi : Integrable (fun z => f z) (P.bind μ) := f.integrable.mono_measure hbound
  have hfM : Measurable (fun z => ENNReal.ofReal (f z)) := f.continuous.measurable.ennreal_ofReal
  rw [← Measure.lintegral_bind (m := P) hμ.aemeasurable hfM.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hf)]
  exact ENNReal.ofReal_ne_top

lemma positive_kernel_test_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hbound : P.bind μ ≤ initialGreenMeasure κ)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    Integrable (fun ω => ∫ z, f z ∂μ ω) P := by
  have hq : Measurable (fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂μ ω) :=
    (Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp hμ
  have hi := integrable_toReal_of_lintegral_ne_top hq.aemeasurable
    (positive_kernel_test_lintegral_ne_top P κ μ hμ hbound f hf)
  convert hi using 1
  funext ω
  exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) f.continuous.measurable.aestronglyMeasurable

lemma positive_kernel_integral_bind
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ)
    (hbound : P.bind μ ≤ initialGreenMeasure κ)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) :
    (∫ ω, ∫ z, f z ∂μ ω ∂P) = ∫ z, f z ∂P.bind μ := by
  have hq : Measurable (fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂μ ω) :=
    (Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal).comp hμ
  have he (ω : Ω) : (∫ z, f z ∂μ ω)=(∫⁻ z, ENNReal.ofReal (f z) ∂μ ω).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) f.continuous.measurable.aestronglyMeasurable
  have hfM : Measurable (fun z => ENNReal.ofReal (f z)) := f.continuous.measurable.ennreal_ofReal
  simp_rw [he]
  rw [integral_toReal hq.aemeasurable
    (ae_lt_top hq (positive_kernel_test_lintegral_ne_top P κ μ hμ hbound f hf)),
    ← Measure.lintegral_bind (m := P) hμ.aemeasurable hfM.aemeasurable]
  exact (integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf)
    f.continuous.measurable.aestronglyMeasurable).symm

end SLEExactGauge.Multipoint

end

end OAI
