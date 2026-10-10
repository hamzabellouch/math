import OAI.Analysis.CircleDomains.Topology.PathTolls
import OAI.Analysis.CircleDomains.Probability.IntervalPaymentNullImage
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! The local tag cost is an actual measure on parameter time: a
weighted physical-length part plus one atom for each flagged visit. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

def boundaryTimeMeasure {X : Type*} (γ : PathTime → X) (m : X → ℝ≥0∞) :
    Measure PathTime :=
  Measure.sum (fun t => m (γ t) • Measure.dirac t)

theorem boundaryTimeMeasure_apply {X : Type*} (γ : PathTime → X) (m : X → ℝ≥0∞)
    {S : Set PathTime} (hS : MeasurableSet S) :
    boundaryTimeMeasure γ m S = ∑' t, m (γ t) * S.indicator 1 t := by
  simp only [boundaryTimeMeasure, Measure.sum_apply _ hS, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ hS]

theorem boundaryTimeMeasure_univ {X : Type*} [MetricSpace X]
    (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    boundaryTimeMeasure γ m univ = boundaryToll γ m := by
  simp only [boundaryTimeMeasure_apply γ m MeasurableSet.univ, indicator_univ,
    Pi.one_apply, mul_one, boundaryToll]

def tagPaymentMeasure {X : Type*} (μ : Measure PathTime) (g : PathTime → ℝ≥0∞)
    (γ : PathTime → X) (m : X → ℝ≥0∞) : Measure PathTime :=
  μ.withDensity g + boundaryTimeMeasure γ m

theorem tagPaymentMeasure_univ {X : Type*} [MetricSpace X]
    (μ : Measure PathTime) (g : PathTime → ℝ≥0∞)
    (γ : C(PathTime, X)) (m : X → ℝ≥0∞) :
    tagPaymentMeasure μ g γ m univ = (∫⁻ t, g t ∂μ) + boundaryToll γ m := by
  rw [tagPaymentMeasure, Measure.add_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, boundaryTimeMeasure_univ]

theorem tagPaymentMeasure_finite {X : Type*} [MetricSpace X]
    (μ : Measure PathTime) (g : PathTime → ℝ≥0∞)
    (γ : C(PathTime, X)) (m : X → ℝ≥0∞)
    (hcost : (∫⁻ t, g t ∂μ) + boundaryToll γ m < ∞) :
    IsFiniteMeasure (tagPaymentMeasure μ g γ m) := by
  constructor
  rwa [tagPaymentMeasure_univ]

theorem tagPaymentMeasure_null_free {X : Type*}
    (μ : Measure PathTime) (g : PathTime → ℝ≥0∞) (γ : PathTime → X) (m : X → ℝ≥0∞)
    {F : Set PathTime} (hF : MeasurableSet F) (hμ : μ F = 0)
    (hm : ∀ t ∈ F, m (γ t) = 0) :
    tagPaymentMeasure μ g γ m F = 0 := by
  rw [tagPaymentMeasure, Measure.add_apply, withDensity_apply _ hF,
    Measure.restrict_eq_zero.mpr hμ, lintegral_zero_measure, zero_add,
    boundaryTimeMeasure_apply γ m hF]
  apply ENNReal.tsum_eq_zero.mpr
  intro t
  by_cases ht : t ∈ F
  · rw [hm t ht, zero_mul]
  · simp only [indicator_of_notMem ht, mul_zero]

/-- Paying once at each distinct image point is bounded by paying at every visit. -/
theorem boundaryTimeMeasure_image_le {X : Type*} (γ : PathTime → X) (m : X → ℝ≥0∞)
    {S : Set PathTime} (hS : MeasurableSet S) {A : Set X} (hA : A ⊆ γ '' S) :
    (∑' x : A, m x.val) ≤ boundaryTimeMeasure γ m S := by
  classical
  choose τ hτ hγ using fun x : A => hA x.property
  have hinj : Function.Injective τ := by
    intro x y hxy
    apply Subtype.ext
    exact (hγ x).symm.trans ((congrArg γ hxy).trans (hγ y))
  rw [boundaryTimeMeasure_apply γ m hS]
  calc
    (∑' x : A, m x.val) = ∑' x : A, m (γ (τ x)) * S.indicator 1 (τ x) := by
      apply tsum_congr
      intro x
      simp only [hγ x, indicator_of_mem (hτ x), Pi.one_apply, mul_one]
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun t => m (γ t) * S.indicator 1 t)

end CircleDomainRigidity

end

end OAI
