import OAI.Probability.SLE.Geometry.FiniteStoppedScalar

namespace OAI

/-! Equality of densities on stopped-past events also identifies every
nonnegative measurable test of that same past. -/
noncomputable section
open Set _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ENNReal

namespace SLEExactGauge

lemma past_density_test_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω)
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (M : Ω → ℝ≥0∞) (hM : Measurable[m] M) (E : Set Ω) (hE : MeasurableSet[m] E)
    (hmean : ∀ A : Set Ω, MeasurableSet[m] A → (∫⁻ ω in A∩E, M ω ∂P)=Q (A∩E))
    (f : Ω → ℝ≥0∞) (hf : Measurable[m] f)
    (A : Set Ω) (hA : MeasurableSet[m] A) :
    (∫⁻ ω in A∩E, M ω*f ω ∂P)=(∫⁻ ω in A∩E, f ω ∂Q) := by
  have heq (D : Set Ω) (hD : MeasurableSet[m] D) :
      ((P.withDensity M).restrict E) D=(Q.restrict E) D := by
    rw [Measure.restrict_apply (hm _ hD),Measure.restrict_apply (hm _ hD),
      withDensity_apply _ (hm _ (hD.inter hE))]
    exact hmean D hD
  have hh := @lintegral_eq_of_stopped_events Ω mΩ ((P.withDensity M).restrict E) (Q.restrict E)
    m hm heq (A.indicator f) (hf.indicator hA)
  rw [lintegral_indicator (hm _ hA),lintegral_indicator (hm _ hA),
    Measure.restrict_restrict (hm _ hA),Measure.restrict_restrict (hm _ hA),
    setLIntegral_withDensity_eq_setLIntegral_mul P (hM.mono hm le_rfl)
      (hf.mono hm le_rfl) (hm _ (hA.inter hE))] at hh
  exact hh

end SLEExactGauge

end

end OAI
