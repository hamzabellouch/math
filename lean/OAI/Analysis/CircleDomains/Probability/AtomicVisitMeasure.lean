import OAI.Analysis.CircleDomains.Selection.PreterminalVisits
import Mathlib.MeasureTheory.Measure.GiryMonad

namespace OAI

/-! The countable atomic part of a path's coding measure, using actual
preterminal visit multiplicity and prescribed positive point weights. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X D : Type*} [MetricSpace X] [MeasurableSpace D]

def atomicVisitMeasure (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X)) : Measure D :=
  Measure.sum (fun s => (c s * preterminalVisitCount γ (p s)) • Measure.dirac s)

theorem atomicVisitMeasure_apply (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X))
    {A : Set D} (hA : MeasurableSet A) :
    atomicVisitMeasure p c γ A =
      ∑' s, (c s * preterminalVisitCount γ (p s)) * A.indicator 1 s := by
  simp only [atomicVisitMeasure, Measure.sum_apply _ hA, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hA]

theorem atomicVisitMeasure_univ (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X)) :
    atomicVisitMeasure p c γ univ = ∑' s, c s * preterminalVisitCount γ (p s) := by
  simp only [atomicVisitMeasure_apply p c γ MeasurableSet.univ, indicator_univ,
    Pi.one_apply, mul_one]

theorem lintegral_atomicVisitMeasure (p : D → X) (c : D → ℝ≥0∞) (γ : C(PathTime, X))
    (f : D → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f s ∂atomicVisitMeasure p c γ =
      ∑' s, (c s * preterminalVisitCount γ (p s)) * f s := by
  rw [atomicVisitMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf, smul_eq_mul]

variable [Countable D] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_atomicVisitMeasure (p : D → X) (c : D → ℝ≥0∞) :
    Measurable (atomicVisitMeasure p c) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [atomicVisitMeasure_apply p c _ hA]
  apply Measurable.tsum
  intro s
  exact (measurable_const.mul (measurable_preterminalVisitCount.comp
    (measurable_id.prodMk measurable_const))).mul_const _

end CircleDomainRigidity

end

end OAI
