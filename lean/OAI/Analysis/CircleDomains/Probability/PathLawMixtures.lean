import OAI.Analysis.CircleDomains.Probability.PathHitLaws
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! Borel mixtures of actual path laws. Hit probabilities obey the mixture identity;
their finite nonnegative weighted bounds pass to arbitrary probability mixtures.
The dual finite bounds imply square summability and countable positive support. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]

def probabilityMixture (P : ProbabilityMeasure Z) (law : Z → ProbabilityMeasure Ω)
    (hlaw : Measurable law) : ProbabilityMeasure Ω :=
  ⟨(P : Measure Z).bind (fun z => (law z : Measure Ω)),
    isProbabilityMeasure_bind
      (measurable_subtype_coe.comp hlaw).aemeasurable
      (Eventually.of_forall fun _ => inferInstance)⟩

theorem probabilityMixture_apply (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure Ω) (hlaw : Measurable law)
    {E : Set Ω} (hE : MeasurableSet E) :
    (probabilityMixture P law hlaw : Measure Ω) E =
      ∫⁻ z, (law z : Measure Ω) E ∂(P : Measure Z) :=
  Measure.bind_apply hE (measurable_subtype_coe.comp hlaw).aemeasurable

section Paths

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

def pathHitReal (μ : ProbabilityMeasure C(PathTime, X)) (x : X) : ℝ :=
  (pathHitProbability μ x).toReal

omit [BorelSpace C(PathTime, X)] in
theorem pathHitReal_nonneg (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    0 ≤ pathHitReal μ x := ENNReal.toReal_nonneg

omit [BorelSpace C(PathTime, X)] in
theorem pathHitReal_le_one (μ : ProbabilityMeasure C(PathTime, X)) (x : X) :
    pathHitReal μ x ≤ 1 := by
  simpa only [pathHitReal, ENNReal.toReal_one] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞)
    (pathHitProbability_le_one μ x)

theorem measurable_pathHitProbability (x : X) :
    Measurable (fun μ : ProbabilityMeasure C(PathTime, X) => pathHitProbability μ x) :=
  (Measure.measurable_coe (isClosed_paths_hitting x).measurableSet).comp
    measurable_subtype_coe

theorem integrable_pathHitReal (P : ProbabilityMeasure Z)
    {law : Z → ProbabilityMeasure C(PathTime, X)} (hlaw : Measurable law) (x : X) :
    Integrable (fun z => pathHitReal (law z) x) (P : Measure Z) := by
  apply Integrable.of_bound
    (((measurable_pathHitProbability x).comp hlaw).ennreal_toReal.aestronglyMeasurable) 1
  exact Eventually.of_forall fun z => by
    change ‖pathHitReal (law z) x‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (pathHitReal_nonneg _ _)]
    exact pathHitReal_le_one _ _

theorem pathHitProbability_mixture (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure C(PathTime, X)) (hlaw : Measurable law) (x : X) :
    pathHitProbability (probabilityMixture P law hlaw) x =
      ∫⁻ z, pathHitProbability (law z) x ∂(P : Measure Z) :=
  probabilityMixture_apply P law hlaw (isClosed_paths_hitting x).measurableSet

theorem pathHitReal_mixture (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure C(PathTime, X)) (hlaw : Measurable law) (x : X) :
    pathHitReal (probabilityMixture P law hlaw) x =
      ∫ z, pathHitReal (law z) x ∂(P : Measure Z) := by
  rw [pathHitReal, pathHitProbability_mixture]
  exact (integral_toReal ((measurable_pathHitProbability x).comp hlaw).aemeasurable
    (Eventually.of_forall fun z => lt_of_le_of_lt
      (pathHitProbability_le_one (law z) x) (by simp))).symm

/-- The finite nonnegative dual tests for the square norm of the hit vector. -/
def HasHitNormBound (μ : ProbabilityMeasure C(PathTime, X)) (C : ℝ) : Prop :=
  ∀ (F : Finset X) (w : X → ℝ), (∀ x ∈ F, 0 ≤ w x) →
    ∑ x ∈ F, w x * pathHitReal μ x ≤ C * Real.sqrt (∑ x ∈ F, w x ^ 2)

theorem HasHitNormBound.mixture (P : ProbabilityMeasure Z)
    (law : Z → ProbabilityMeasure C(PathTime, X)) (hlaw : Measurable law)
    {C : ℝ} (hbound : ∀ᵐ z ∂(P : Measure Z), HasHitNormBound (law z) C) :
    HasHitNormBound (probabilityMixture P law hlaw) C := by
  intro F w hw
  have hi (x : X) : Integrable (fun z => w x * pathHitReal (law z) x) (P : Measure Z) :=
    (integrable_pathHitReal P hlaw x).const_mul (w x)
  calc
    ∑ x ∈ F, w x * pathHitReal (probabilityMixture P law hlaw) x =
        ∫ z, ∑ x ∈ F, w x * pathHitReal (law z) x ∂(P : Measure Z) := by
      simp_rw [pathHitReal_mixture, ← integral_const_mul]
      exact (integral_finsetSum F fun x _ => hi x).symm
    _ ≤ ∫ _ : Z, C * Real.sqrt (∑ x ∈ F, w x ^ 2) ∂(P : Measure Z) :=
      integral_mono_ae (integrable_finsetSum F fun x _ => hi x) (integrable_const _)
        (hbound.mono fun _ hz => hz F w hw)
    _ = C * Real.sqrt (∑ x ∈ F, w x ^ 2) := by simp

omit [BorelSpace C(PathTime, X)] in
theorem HasHitNormBound.sum_sq_le {μ : ProbabilityMeasure C(PathTime, X)} {C : ℝ}
    (hbound : HasHitNormBound μ C) (F : Finset X) :
    ∑ x ∈ F, pathHitReal μ x ^ 2 ≤ C ^ 2 := by
  have h := hbound F (pathHitReal μ) (fun x _ => pathHitReal_nonneg μ x)
  simp only [← sq] at h
  have hs : 0 ≤ ∑ x ∈ F, pathHitReal μ x ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsqrt := Real.sq_sqrt hs
  have hp := Real.sqrt_nonneg (∑ x ∈ F, pathHitReal μ x ^ 2)
  nlinarith [sq_nonneg (Real.sqrt (∑ x ∈ F, pathHitReal μ x ^ 2) - C)]

omit [BorelSpace C(PathTime, X)] in
theorem HasHitNormBound.summable_sq {μ : ProbabilityMeasure C(PathTime, X)} {C : ℝ}
    (hbound : HasHitNormBound μ C) :
    Summable (fun x => pathHitReal μ x ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) hbound.sum_sq_le

omit [BorelSpace C(PathTime, X)] in
theorem HasHitNormBound.countable_positive_support
    {μ : ProbabilityMeasure C(PathTime, X)} {C : ℝ}
    (hbound : HasHitNormBound μ C) :
    {x | 0 < pathHitProbability μ x}.Countable := by
  apply hbound.summable_sq.countable_support.mono
  intro x hx
  change pathHitReal μ x ^ 2 ≠ 0
  apply pow_ne_zero
  exact ne_of_gt (ENNReal.toReal_pos (ne_of_gt hx)
    (ne_of_lt (lt_of_le_of_lt (pathHitProbability_le_one μ x) (by simp))))

end Paths

end CircleDomainRigidity

end

end OAI
