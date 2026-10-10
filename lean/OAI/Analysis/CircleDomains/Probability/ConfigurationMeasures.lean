import OAI.Analysis.CircleDomains.Selection.HitConfigurations
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace OAI

/-! Actual finite atomic measures associated to weighted configurations, and
their probability barycenters. Integrals against the barycenter are exactly
the expected weighted configuration integrals. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {n : ℕ} {r : ℝ}

def configurationMeasure (p : HitConfiguration X n r) : Measure X :=
  ∑ i, ENNReal.ofReal (p.val.2 i : ℝ) • Measure.dirac (p.val.1 i)

theorem measurable_configurationMeasure :
    Measurable (configurationMeasure (X := X) (n := n) (r := r)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [configurationMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.mul
  · exact (by fun_prop : Continuous (fun p : HitConfiguration X n r => (p.val.2 i : ℝ))).measurable.ennreal_ofReal
  · exact (Measure.measurable_coe hs).comp
      (Measure.measurable_dirac.comp (by fun_prop : Continuous (fun p : HitConfiguration X n r => p.val.1 i)).measurable)

omit [SecondCountableTopology X] [BorelSpace X] in
theorem lintegral_configurationMeasure (p : HitConfiguration X n r)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂configurationMeasure p =
      ∑ i, ENNReal.ofReal (p.val.2 i : ℝ) * f (p.val.1 i) := by
  rw [configurationMeasure, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

omit [SecondCountableTopology X] [BorelSpace X] in
theorem configurationMeasure_mass_le (p : HitConfiguration X n r) :
    configurationMeasure p univ ≤ n := by
  have h := lintegral_configurationMeasure p measurable_const
    (f := fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, mul_one] at h
  rw [h]
  calc
    ∑ i : Fin n, ENNReal.ofReal (p.val.2 i : ℝ) ≤ ∑ _i : Fin n, (1 : ℝ≥0∞) :=
      Finset.sum_le_sum fun i _ => by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (p.val.2 i).property.2
    _ = n := by simp

def meanConfigurationMeasure (P : ProbabilityMeasure (HitConfiguration X n r)) : Measure X :=
  (P : Measure (HitConfiguration X n r)).bind configurationMeasure

theorem lintegral_meanConfigurationMeasure (P : ProbabilityMeasure (HitConfiguration X n r))
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂meanConfigurationMeasure P =
      ∫⁻ p : HitConfiguration X n r, ∑ i, ENNReal.ofReal (p.val.2 i : ℝ) * f (p.val.1 i)
        ∂(P : Measure (HitConfiguration X n r)) := by
  rw [meanConfigurationMeasure, Measure.lintegral_bind
    measurable_configurationMeasure.aemeasurable hf.aemeasurable]
  exact lintegral_congr fun p => lintegral_configurationMeasure p hf

instance (P : ProbabilityMeasure (HitConfiguration X n r)) :
    IsFiniteMeasure (meanConfigurationMeasure P) := by
  constructor
  rw [meanConfigurationMeasure, Measure.bind_apply MeasurableSet.univ
    (measurable_configurationMeasure (X := X) (n := n) (r := r)).aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono fun p => configurationMeasure_mass_le p)
  simp

end CircleDomainRigidity

end

end OAI
