import OAI.Probability.FreeIsing.Critical.CanonicalResponse
import OAI.Probability.FreeIsing.Ising.RootWeightedCut

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootGaussianCut

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage IsingCopyWeightedCut IsingRootAttenuation IsingRootWeightedCut
open PlantedSymmetry CavityFieldLimit PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def terminalAttenuation (hbeta : 0 ≤ beta) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (infiniteCavityField hbeta (ConnectedHull.takeVertex v (i + 1))
      (ConnectedHull.takeVertex v i) y)

theorem measurable_terminalAttenuation (hbeta : 0 ≤ beta) (v : TreeVertex d) :
    Measurable (terminalAttenuation hbeta v) := by
  unfold terminalAttenuation
  exact Finset.measurable_prod _ (fun i _ =>
    (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
      (measurable_infiniteCavityField hbeta _ _))

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_eq_forward_product
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun p => terminalAttenuation hbeta v (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => ∏ i ∈ Finset.range v.1.length,
        responseAttenuation (Real.tanh beta) (forwardGaussianField μ t v i p) := by
  have hfield (i : Fin v.1.length) :=
    hμ.infiniteCavityField_path_eq_forward_posterior hbeta t v i i.2
  filter_upwards [ae_all_iff.mpr hfield] with p hp
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (responseAttenuation (Real.tanh beta)) (hp ⟨i, Finset.mem_range.mp hi⟩)

def terminalExtensionAverage (hbeta : 0 ≤ beta) (stem : List (Fin d))
    (n k : ℕ) : (TreeVertex d → ℝ) → ℝ :=
  WeightedOrbitAverage.average (fun s : Extension stem n => fun y =>
    terminalAttenuation hbeta (endpoint s) y ^ k)

theorem measurable_terminalExtensionAverage (hbeta : 0 ≤ beta)
    (stem : List (Fin d)) (n k : ℕ) :
    Measurable (terminalExtensionAverage hbeta stem n k) := by
  unfold terminalExtensionAverage WeightedOrbitAverage.average
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun s _ =>
    (measurable_terminalAttenuation hbeta (endpoint s)).pow_const k)

theorem extensionAverage_eq_terminal (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (stem : List (Fin d)) (n k : ℕ) (x : Paths d) :
    extensionAverage hbeta t stem n k x =
      terminalExtensionAverage hbeta stem n k (fun i => x i t) := rfl

omit [IsProbabilityMeasure μ] in
theorem terminalExtensionAverage_eq_forward_average
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (stem : List (Fin d)) (n k : ℕ) :
    (fun p => terminalExtensionAverage hbeta stem n k (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      WeightedOrbitAverage.average (fun s : Extension stem n => fun p =>
        (∏ i ∈ Finset.range (endpoint s).1.length,
          responseAttenuation (Real.tanh beta)
            (forwardGaussianField μ t (endpoint s) i p)) ^ k) := by
  classical
  filter_upwards [ae_all_iff.mpr (fun s : Extension stem n =>
    terminalAttenuation_eq_forward_product hμ hbeta t (endpoint s))] with p hp
  unfold terminalExtensionAverage WeightedOrbitAverage.average
  congr 1
  exact Finset.sum_congr rfl (fun s _ => congrArg (fun z : ℝ => z ^ k) (hp s))

theorem extensionAverage_identDistrib_gaussian (hbeta : 0 ≤ beta) (t : ℝ≥0)
    (left : Bool) (stem : List (Fin d)) (n k : ℕ) :
    IdentDistrib (fun q => extensionAverage hbeta t stem n k (observationCopy left q))
      (fun p => terminalExtensionAverage hbeta stem n k (observation t p))
      (copies beta μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have heval := (hasLaw_observationLaw_eval μ t).comp
    (measurePreserving_observationCopy (beta := beta) (μ := μ) left).hasLaw
  have hobs : HasLaw (observation (ι := TreeVertex d) t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  exact (heval.identDistrib hobs).comp (measurable_terminalExtensionAverage hbeta stem n k)

theorem integral_root_weight_mul_pow_le_gaussian_cut
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (left : Bool) (k : ℕ) {stem : List (Fin d)} {n : ℕ}
    (s₀ : Extension stem n) (m : ℕ)
    (F : ∀ c : TreeShell d m, (RootedBroadcast.DescendantVertex c.1 → IsingSpin) ×
      (RootedBroadcast.DescendantVertex c.1 → ℝ) → ℝ)
    (hF : ∀ c, Measurable (F c)) (hbound : ∀ c p, 0 ≤ F c p ∧ F c p ≤ 1)
    (I : Finset (TreeShell d m)) (hI : I.Nonempty) {τ C : ℝ}
    (hτ : 0 ≤ τ) (hC : 0 ≤ C)
    (hmean : ∀ c ∈ I, (∫ z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ),
      F c ((fun v => z.1 v.1), fun v => z.2 v.1)
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤ τ / 4)
    (hdom : ∀ᵐ z ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      terminalExtensionAverage hbeta stem n k (observation t z) ≤
        C * ActualCutWeightedAverage.average F I z) :
    (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 *
      rootAttenuation hbeta t (endpoint s₀) (observationCopy left q) ^ k ∂copies beta μ) ≤
      (C * τ) * (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 ∂copies beta μ) +
        (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
          Real.exp (-(I.card : ℝ) * τ ^ 2 / 2) := by
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let : IsProbabilityMeasure (observationLaw μ) := inferInstance
  let : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  let : IsProbabilityMeasure (copies beta μ) := by unfold copies; infer_instance
  rw [integral_root_weight_mul_extension_average hμ hbeta t left k s₀]
  have hw := IsingCopyStationarity.integrable_fieldDifference_sq hμ hbeta t
    (ConnectedHull.root d)
  have hmax : ∀ᵐ q ∂copies beta μ, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 ≤
      (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
    filter_upwards [ae_fieldDifference_bound hμ hbeta kernel_graphLaw t
      (ConnectedHull.root d)] with q hq
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hq 2
  exact ActualCutWeightedAverage.integral_mul_le hμ
    (by linarith [tanh_nonneg_of_beta_nonneg hbeta]) (Real.tanh_lt_one beta).le
    m (fun _ => gaussianReal 0 t) F hF hbound I hI hτ hC (sq_nonneg _) hmean
    (extensionAverage_identDistrib_gaussian hbeta t left stem n k) hw
    ((measurable_extensionAverage hbeta t stem n k).comp (measurable_observationCopy left))
    (Filter.Eventually.of_forall (fun q => sq_nonneg _)) hmax
    (Filter.Eventually.of_forall (fun q =>
      (extensionAverage_mem_Icc hbeta t s₀ k (observationCopy left q)).1))
    (Filter.Eventually.of_forall (fun q =>
      (extensionAverage_mem_Icc hbeta t s₀ k (observationCopy left q)).2)) hdom

end Problem367.IsingRootGaussianCut

end

end OAI
