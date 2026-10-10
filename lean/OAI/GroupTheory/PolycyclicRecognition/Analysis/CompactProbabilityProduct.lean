import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling

namespace OAI

/-! # Independent compact sampling and supported limits -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology NNReal

/-- Pushing forward the first independent coordinate is the same as
pushing the joint law through the corresponding product map. -/
theorem productOccupationLaw_map_left
    {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace D]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (f : A → B) (hf : Measurable f) :
    productOccupationLaw (ProbabilityMeasure.map μ f) ν id =
      productOccupationLaw μ ν (Prod.map f id) := by
  apply Subtype.ext
  change Measure.map id ((Measure.map f (μ : Measure A)).prod (ν : Measure D)) =
    Measure.map (Prod.map f id) ((μ : Measure A).prod (ν : Measure D))
  rw [Measure.map_id]
  simpa only [Measure.map_id] using
    (Measure.map_prod_map (μ : Measure A) (ν : Measure D) hf measurable_id)

/-- Integration against a probability is continuous in the uniform norm. -/
theorem continuous_integral_compact_function
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) :
    Continuous (fun f : C(X, ℝ) => ∫ x, f x ∂(μ : Measure X)) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro f g
  have hi (h : C(X, ℝ)) : Integrable h (μ : Measure X) :=
    h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace h)
  rw [dist_eq_norm, ← integral_sub (hi f) (hi g)]
  have hb := norm_integral_le_of_norm_le_const (μ := (μ : Measure X))
    (f := fun x => f x - g x) (C := ‖f - g‖)
    (Eventually.of_forall (fun x => (f - g).norm_coe_le_norm x))
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one,
    NNReal.coe_one, one_mul, dist_eq_norm] using hb

/-- A fixed independent coordinate preserves weak convergence of the
profile law. No rate in the other coordinate is required. -/
theorem productOccupationLaw_tendsto_fixed
    {A D ι : Type*} [TopologicalSpace A] [CompactSpace A]
    [TopologicalSpace D] [CompactSpace D] [SecondCountableTopology D]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace D] [BorelSpace D]
    {l : Filter ι} (μs : ι → ProbabilityMeasure A) (μ : ProbabilityMeasure A)
    (hμ : Tendsto μs l (𝓝 μ)) (ν : ProbabilityMeasure D) :
    Tendsto (fun i => productOccupationLaw (μs i) ν id) l
      (𝓝 (productOccupationLaw μ ν id)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let fc : C(A × D, ℝ) := f.toContinuousMap
  let avg : C(A, ℝ) := ⟨fun a => ∫ z, fc (a, z) ∂(ν : Measure D),
    (continuous_integral_compact_function ν).comp fc.curry.continuous⟩
  have h := (ProbabilityMeasure.continuous_integral_continuousMap avg).tendsto μ |>.comp hμ
  change Tendsto (fun i => ∫ x, fc x ∂(productOccupationLaw (μs i) ν id : Measure _)) l
    (𝓝 (∫ x, fc x ∂(productOccupationLaw μ ν id : Measure _)))
  simp_rw [integral_productOccupationLaw _ _ id measurable_id fc]
  exact h

/-- Every pair of supported points is supported by independent sampling. -/
theorem mem_support_productOccupationLaw
    {A D : Type*} [TopologicalSpace A] [TopologicalSpace D]
    [MeasurableSpace A] [MeasurableSpace D]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    {a : A} {d : D} (ha : a ∈ (μ : Measure A).support)
    (hd : d ∈ (ν : Measure D).support) :
    (a, d) ∈ (productOccupationLaw μ ν id : Measure (A × D)).support := by
  apply (Measure.mem_support_iff_forall (a, d)).mpr
  intro U hU
  rw [nhds_prod_eq] at hU
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := mem_prod_iff.mp hU
  have hp := (Measure.mem_support_iff_forall a).mp ha P hP
  have hq := (Measure.mem_support_iff_forall d).mp hd Q hQ
  change 0 < Measure.map id ((μ : Measure A).prod (ν : Measure D)) U
  rw [Measure.map_id]
  have hpq : 0 < (μ : Measure A).prod (ν : Measure D) (P ×ˢ Q) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos hp.ne' hq.ne'
  exact hpq.trans_le (measure_mono hPQ)

end PolycyclicRecognition

end

end OAI
