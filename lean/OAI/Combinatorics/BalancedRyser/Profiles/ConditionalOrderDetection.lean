import OAI.Combinatorics.BalancedRyser.Probability.ConditionalOrderVariance
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionConcentration

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Balanced.ConditionalOrderDetection

open ConditionalOrderVariance UncoveredSampling

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def planeObservable (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) (p : OrderPair U V) : ℝ :=
  planeFraction (populationLines U (I.map p.1.toEmbedding))
    (populationLines V (J.map p.2.toEmbedding))

noncomputable def targetObservable (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) (x : U) (p : OrderPair U V) : ℝ :=
  targetFraction x.val (populationLines U (I.map p.1.toEmbedding))
    (populationLines V (J.map p.2.toEmbedding))

private theorem finite_memLp {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) : MemLp f 2 μ := by
  apply MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable
    (∑ ω, |f ω|)
  apply Filter.Eventually.of_forall
  intro ω
  simp only [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun z _ => abs_nonneg (f z)) (Finset.mem_univ ω)

section Conditional

variable (U V : Finset (Line F))
variable [MeasurableSpace (OrderPair U V)] [MeasurableSingletonClass (OrderPair U V)]
variable (I : Finset U) (J : Finset V) (i x : U)

theorem unmarked_probability_le_of_mean_gap
    (hUV : Disjoint U V) (hi : i ∉ I) {ε : ℝ} (hε : 0 < ε)
    (hgap : 2 * ε <
      |(∫ p, targetObservable U V I J x p ∂(conditionedOrderLaw U V i x).toMeasure) -
        ∫ p, planeObservable U V I J p ∂(conditionedOrderLaw U V i x).toMeasure|) :
    (conditionedOrderLaw U V i x).toMeasure.real
      {p | |targetObservable U V I J x p - planeObservable U V I J p| ≤ ε} ≤
      32 * ((I.card : ℝ) + J.card) / ((Fintype.card F : ℝ)^2 * ε^2) := by
  have h := ProfileDetectionConcentration.unmarked_probability_le_of_mean_gap
    (finite_memLp _ (targetObservable U V I J x))
    (finite_memLp _ (planeObservable U V I J)) hε hgap
  have htarget := target_conditioned_order_measure_variance_le U V hUV I J i x hi
  have hplane := plane_conditioned_order_measure_variance_le U V I J i x hi
  calc
    _ ≤ 4 * (variance (targetObservable U V I J x)
        (conditionedOrderLaw U V i x).toMeasure +
      variance (planeObservable U V I J)
        (conditionedOrderLaw U V i x).toMeasure) / ε^2 := h
    _ ≤ 4 * (4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2 +
        4 * ((I.card : ℝ) + J.card) / (Fintype.card F : ℝ)^2) / ε^2 := by
      gcongr
      · exact htarget
      · exact hplane
    _ = _ := by ring

theorem unmarked_probability_le_of_profile_gap
    (hUV : Disjoint U V) (hi : i ∉ I) {a b ε : ℝ}
    (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hTa : |(∫ p, targetObservable U V I J x p
        ∂(conditionedOrderLaw U V i x).toMeasure) - a| ≤ ε / 2)
    (hPb : |(∫ p, planeObservable U V I J p
        ∂(conditionedOrderLaw U V i x).toMeasure) - b| ≤ ε / 2) :
    (conditionedOrderLaw U V i x).toMeasure.real
      {p | |targetObservable U V I J x p - planeObservable U V I J p| ≤ ε} ≤
      32 * ((I.card : ℝ) + J.card) / ((Fintype.card F : ℝ)^2 * ε^2) := by
  apply unmarked_probability_le_of_mean_gap U V I J i x hUV hi hε
  have h₁ := abs_sub_le a
    (∫ p, targetObservable U V I J x p ∂(conditionedOrderLaw U V i x).toMeasure) b
  have h₂ := abs_sub_le
    (∫ p, targetObservable U V I J x p ∂(conditionedOrderLaw U V i x).toMeasure)
    (∫ p, planeObservable U V I J p ∂(conditionedOrderLaw U V i x).toMeasure) b
  rw [abs_sub_comm a
    (∫ p, targetObservable U V I J x p ∂(conditionedOrderLaw U V i x).toMeasure)] at h₁
  linarith

theorem marked_probability_ge_of_profile_gap
    (hUV : Disjoint U V) (hi : i ∉ I) {a b ε : ℝ}
    (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hTa : |(∫ p, targetObservable U V I J x p
        ∂(conditionedOrderLaw U V i x).toMeasure) - a| ≤ ε / 2)
    (hPb : |(∫ p, planeObservable U V I J p
        ∂(conditionedOrderLaw U V i x).toMeasure) - b| ≤ ε / 2) :
    1 - 32 * ((I.card : ℝ) + J.card) / ((Fintype.card F : ℝ)^2 * ε^2) ≤
      (conditionedOrderLaw U V i x).toMeasure.real
        {p | ε < |targetObservable U V I J x p - planeObservable U V I J p|} := by
  rw [ProfileDetectionConcentration.marked_probability_eq
    (finite_memLp _ (targetObservable U V I J x))
    (finite_memLp _ (planeObservable U V I J))]
  exact sub_le_sub_left
    (unmarked_probability_le_of_profile_gap U V I J i x hUV hi hε hgap hTa hPb) 1

theorem unmarked_probability_le_scaled
    (hUV : Disjoint U V) (hi : i ∉ I) {a b ε C : ℝ}
    (hε : 0 < ε) (hgap : 3 * ε < |a - b|)
    (hTa : |(∫ p, targetObservable U V I J x p
        ∂(conditionedOrderLaw U V i x).toMeasure) - a| ≤ ε / 2)
    (hPb : |(∫ p, planeObservable U V I J p
        ∂(conditionedOrderLaw U V i x).toMeasure) - b| ≤ ε / 2)
    (hsize : (I.card : ℝ) + J.card ≤ C * Fintype.card F) :
    (conditionedOrderLaw U V i x).toMeasure.real
      {p | |targetObservable U V I J x p - planeObservable U V I J p| ≤ ε} ≤
      32 * C / ((Fintype.card F : ℝ) * ε^2) := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ 32 * ((I.card : ℝ) + J.card) / ((Fintype.card F : ℝ)^2 * ε^2) :=
      unmarked_probability_le_of_profile_gap U V I J i x hUV hi hε hgap hTa hPb
    _ ≤ 32 * (C * Fintype.card F) / ((Fintype.card F : ℝ)^2 * ε^2) := by
      gcongr
    _ = _ := by field_simp

end Conditional

end Balanced.ConditionalOrderDetection

end OAI
