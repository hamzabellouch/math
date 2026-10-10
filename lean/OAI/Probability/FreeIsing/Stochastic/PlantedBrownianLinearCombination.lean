import OAI.Probability.FreeIsing.Brownian.ArrayMoments
import OAI.Probability.FreeIsing.Brownian.LinearCombination

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

lemma iIndepFun_comp_measurePreserving
    {ι Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r : Ω → Ω'} (hr : MeasurePreserving r μ ν)
    {f : ι → Ω' → E} (hf : ∀ i, Measurable (f i)) (hind : iIndepFun f ν) :
    iIndepFun (fun i => f i ∘ r) μ := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun i => (hf i).comp hr.measurable)).2
  have h := hind.map_fun_eq_infinitePi_map hf
  rw [← hr.map_eq] at h
  simpa only [Measure.map_map (Measurable.of_eval hf) hr.measurable,
    Measure.map_map (hf _) hr.measurable, Function.comp_def] using h

theorem planted_coordinate_paths_iIndepFun
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    [∀ i, IsProbabilityMeasure (μ i)]
    {B : ι → ℝ≥0 → Ω → ℝ} (hmB : ∀ i t, Measurable (B i t)) :
    iIndepFun (fun i (q : S × (ι → Ω)) t => B i t (q.2 i))
      (ν.prod (Measure.infinitePi μ)) := by
  have hm (i : ι) : Measurable (fun ω t => B i t ω) :=
    Measurable.of_eval (hmB i)
  exact iIndepFun_comp_measurePreserving measurePreserving_snd
    (fun i => (hm i).comp (measurable_pi_apply i)) (iIndepFun_infinitePi hm)

theorem planted_finite_projection_preBrownian
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) (I : Finset ι) (a : ι → ℝ)
    (ha : ∑ i ∈ I, a i ^ 2 = 1) :
    IsPreBrownianReal (fun t (q : S × (ι → Ω)) => ∑ i ∈ I, a i * B i t (q.2 i))
      (ν.prod (Measure.infinitePi μ)) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hind := (planted_coordinate_paths_iIndepFun ν μ hmB).precomp
    (show Function.Injective (fun i : I => (i : ι)) from Subtype.val_injective)
  have h := BrownianLinearCombination.isPreBrownianReal_sum
    (fun i : I => planted_coordinate_preBrownian ν μ hB i) hind
    (fun i : I => a i) (by rw [Finset.sum_coe_sort I (fun i => a i ^ 2)]; exact ha)
  convert h using 1
  funext t q
  exact (Finset.sum_coe_sort I (fun i => a i * B i t (q.2 i))).symm

theorem planted_finite_projection_normalized_preBrownian
    {ι S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) (μ : ι → Measure Ω) [IsProbabilityMeasure ν]
    {B : ι → ℝ≥0 → Ω → ℝ} (hB : ∀ i, IsPreBrownianReal (B i) (μ i))
    (hmB : ∀ i t, Measurable (B i t)) (I : Finset ι) (a : ι → ℝ)
    (ha : 0 < ∑ i ∈ I, a i ^ 2) :
    IsPreBrownianReal (fun t (q : S × (ι → Ω)) =>
      (Real.sqrt (∑ i ∈ I, a i ^ 2))⁻¹ * ∑ i ∈ I, a i * B i t (q.2 i))
      (ν.prod (Measure.infinitePi μ)) := by
  classical
  have (i : ι) : IsProbabilityMeasure (μ i) :=
    (hB i).isGaussianProcess.isProbabilityMeasure
  have hind := (planted_coordinate_paths_iIndepFun ν μ hmB).precomp
    (show Function.Injective (fun i : I => (i : ι)) from Subtype.val_injective)
  have h := BrownianLinearCombination.isPreBrownianReal_normalized_sum
    (fun i : I => planted_coordinate_preBrownian ν μ hB i) hind
    (fun i : I => a i) (by rw [Finset.sum_coe_sort I (fun i => a i ^ 2)]; exact ha)
  convert h using 1
  funext t q
  rw [Finset.sum_coe_sort I (fun i => a i ^ 2),
    Finset.sum_coe_sort I (fun i => a i * B i t (q.2 i))]

end Problem367

end

end OAI
