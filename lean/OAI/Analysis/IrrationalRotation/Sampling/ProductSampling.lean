import OAI.Analysis.IrrationalRotation.Model.ProductSampling
import OAI.Analysis.IrrationalRotation.Analysis.TriangularMarginals
import Mathlib

namespace OAI

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel.Sampling

theorem representative_mem_Ico (x : Circle) : circleRepresentative x ∈ Ico (0 : ℝ) 1 := by
  simpa [circleRepresentative] using (AddCircle.equivIco (1 : ℝ) 0 x).property

@[fun_prop]
theorem representative_measurable : Measurable circleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

@[fun_prop]
theorem selectedEndpoint_measurable (I : Finset ℕ) :
    Measurable (fun xz : EndpointPair => selectedEndpoint I xz.1 xz.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ I
  · simpa [selectedEndpoint, hi, Function.comp_def] using (measurable_pi_apply i).comp measurable_snd
  · simpa [selectedEndpoint, hi, Function.comp_def] using (measurable_pi_apply i).comp measurable_fst

@[fun_prop]
theorem endpointMap_measurable (I : Finset ℕ) :
    Measurable (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2)) :=
  measurable_fst.prodMk (selectedEndpoint_measurable I)

theorem triangularEvent_measurable (I : Finset ℕ) : MeasurableSet (triangularEvent I) := by
  unfold triangularEvent
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact measurableSet_lt
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem ordered_measurable : MeasurableSet {xy : EndpointPair | Ordered xy.1 xy.2} := by
  unfold Ordered
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem triangularLaw_finite (I : Finset ℕ) : IsFiniteMeasure (triangularLaw I) := by
  unfold triangularLaw
  infer_instance

theorem triangularLaw_ordered (I : Finset ℕ) :
    ∀ᵐ xy ∂triangularLaw I, Ordered xy.1 xy.2 := by
  unfold triangularLaw
  rw [ae_map_iff (endpointMap_measurable I).aemeasurable ordered_measurable]
  filter_upwards [ae_restrict_mem (triangularEvent_measurable I)] with xz hxz
  intro i
  by_cases hi : i ∈ I
  · simpa [selectedEndpoint, hi] using (hxz i hi).le
  · simp [selectedEndpoint, hi]

theorem triangular_density_bounds (I : Finset ℕ) (x : Base) :
    (0 ≤ triangularFirstDensity I x ∧ triangularFirstDensity I x ≤ 1) ∧
    (0 ≤ triangularSecondDensity I x ∧ triangularSecondDensity I x ≤ 1) := by
  have hrep (i : ℕ) := representative_mem_Ico (x i)
  constructor
  · constructor
    · exact Finset.prod_nonneg (fun i _ => by linarith [(hrep i).2])
    · exact Finset.prod_le_one₀ (fun i _ => by linarith [(hrep i).2])
        (fun i _ => by linarith [(hrep i).1])
  · constructor
    · exact Finset.prod_nonneg (fun i _ => (hrep i).1)
    · exact Finset.prod_le_one₀ (fun i _ => (hrep i).1) (fun i _ => (hrep i).2.le)

theorem circleMeasure_singleton (x : Circle) : circleMeasure {x} = 0 := by
  simpa [circleMeasure, Metric.closedBall_zero] using
    (AddCircle.volume_closedBall (1 : ℝ) (x := x) 0)

theorem representative_map_haar :
    circleMeasure.map circleRepresentative = volume.restrict (Ico (0 : ℝ) 1) := by
  exact CocycleSupport.measurePreserving_circleRepresentative.map_eq

theorem representative_tail_measure {a : ℝ} (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) :
    circleMeasure {x | a < circleRepresentative x} = ENNReal.ofReal (1 - a) := by
  exact Invariant233.ProductModel.circleRepresentative_upper_tail a ha0

theorem representative_initial_measure {a : ℝ} (_ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    circleMeasure {x | circleRepresentative x < a} = ENNReal.ofReal a := by
  exact Invariant233.ProductModel.circleRepresentative_lower_tail a ha1

theorem upper_box_measure (I : Finset ℕ) (x : Base) :
    baseMeasure {z | ∀ i ∈ I, circleRepresentative (x i) < circleRepresentative (z i)} =
      ENNReal.ofReal (triangularFirstDensity I x) := by
  exact Invariant233.ProductModel.triangularEvent_fiber_mass I x

theorem lower_box_measure (I : Finset ℕ) (y : Base) :
    baseMeasure {x | ∀ i ∈ I, circleRepresentative (x i) < circleRepresentative (y i)} =
      ENNReal.ofReal (triangularSecondDensity I y) := by
  exact Invariant233.ProductModel.reversedTriangularEvent_fiber_mass I y

theorem triangularLaw_first_marginal (I : Finset ℕ) :
    (triangularLaw I).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularFirstDensity I x)) := by
  exact Invariant233.ProductModel.triangularLaw_first_marginal I

theorem reversedRestriction_first_marginal (I : Finset ℕ) :
    ((baseMeasure.prod baseMeasure).restrict (Prod.swap ⁻¹' triangularEvent I)).map Prod.fst =
      baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularSecondDensity I x)) := by
  exact Invariant233.ProductModel.reversedTriangularEvent_first_marginal I

end Invariant233.ProductModel.Sampling

end OAI
