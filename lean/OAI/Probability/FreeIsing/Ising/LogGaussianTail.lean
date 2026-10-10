import OAI.Probability.FreeIsing.Ising.LogWeightedOrbitCut
import OAI.Probability.FreeIsing.Ising.RootGaussianCut

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingLogGaussianTail

open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open IsingCopyPathBounds IsingCopyWeightedCut IsingRootAttenuation
open IsingRootWeightedCut IsingRootGaussianCut IsingLogWeightedOrbitCut TreeOrbitAverage
open PlantedSymmetry

theorem integral_path_weight_mul_pow_le_of_gaussian_tail
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    {ι : Type*} (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t T : ℝ≥0} (ht : t ≤ T) (s : Finset ι)
    (e : ι → TreeVertex d × TreeVertex d) (left : Bool) (k : ℕ)
    {stem : List (Fin d)} {n : ℕ}
    (hstem : ∀ i ∈ s, (e i).1.1.length ≤ stem.length ∧
      (e i).2.1.length ≤ stem.length) (s₀ : Extension stem n)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 ≤ ε)
    (htail : (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      {p | a < terminalExtensionAverage hbeta stem n k (observation t p)} ≤
        ENNReal.ofReal ε) :
    (∫ q, pathLogDifference hbeta t s e q ^ 2 *
      rootAttenuation hbeta t (endpoint s₀) (observationCopy left q) ^ k ∂copies beta μ) ≤
      a * (∫ q, pathLogDifference hbeta t s e q ^ 2 ∂copies beta μ) +
        ((s.card : ℝ) ^ 2 * edgeLogBound d beta T ^ 2) * ε := by
  rw [integral_path_weight_mul_extension_average hμ hbeta t s e left k hstem s₀]
  have hprob : (copies beta μ)
      {q | a < extensionAverage hbeta t stem n k (observationCopy left q)} ≤
        ENNReal.ofReal ε := by
    have heq : (copies beta μ)
        {q | a < extensionAverage hbeta t stem n k (observationCopy left q)} =
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          {p | a < terminalExtensionAverage hbeta stem n k (observation t p)} :=
      (extensionAverage_identDistrib_gaussian (μ := μ) hbeta t left stem n k).measure_mem_eq
        measurableSet_Ioi
    exact heq.trans_le htail
  exact DependentWeight.integral_mul_le_of_tail_probability
    (integrable_pathLogDifference_sq hμ hbeta t s e)
    ((measurable_extensionAverage hbeta t stem n k).comp (measurable_observationCopy left))
    ha (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (Filter.Eventually.of_forall (fun q => sq_nonneg _))
    (ae_pathLogDifference_sq_bound hμ hbeta ht s e)
    (Filter.Eventually.of_forall (fun q =>
      (extensionAverage_mem_Icc hbeta t s₀ k (observationCopy left q)).1))
    (Filter.Eventually.of_forall (fun q =>
      (extensionAverage_mem_Icc hbeta t s₀ k (observationCopy left q)).2))
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob).trans_eq (ENNReal.toReal_ofReal hε))

end Problem367.IsingLogGaussianTail

end

end OAI
