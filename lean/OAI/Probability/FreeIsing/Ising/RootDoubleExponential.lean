import OAI.Probability.FreeIsing.Gaussian.CutChannels
import OAI.Probability.FreeIsing.Ising.RootGaussianCut

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367.IsingRootDoubleExponential
open IsingObservationInnovation IsingObservationFactor IsingConditionalCopyBounds
open TreeOrbitAverage IsingCopyWeightedCut IsingRootAttenuation IsingRootWeightedCut
open IsingRootGaussianCut PlantedSymmetry PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem rootPathProduct_gaussian_eq_square (t : ℝ≥0) (v : TreeVertex d) (z) :
    rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) z) v =
      (∏ i ∈ Finset.range v.1.length,
        responseAttenuation (Real.tanh beta) (forwardGaussianField μ t v i z)) ^ 2 := by
  rw [← Finset.prod_pow]
  rfl

omit [IsProbabilityMeasure μ] in
theorem terminalExtensionAverage_eq_shell_average
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (n : ℕ) :
    (fun p => terminalExtensionAverage hbeta [] n 2 (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => (∑ v : TreeShell d n,
        rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) p) v.1) /
          (Fintype.card (TreeShell d n) : ℝ) := by
  filter_upwards [terminalExtensionAverage_eq_forward_average hμ hbeta t [] n 2]
    with p hp
  rw [hp]
  unfold WeightedOrbitAverage.average
  rw [Fintype.card_congr (extensionNilEquivTreeShell d n)]
  have hs := (extensionNilEquivTreeShell d n).sum_comp
    (fun v : TreeShell d n => rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) p) v.1)
  have heq (s : Extension ([] : List (Fin d)) n) :
      rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) p)
        ((extensionNilEquivTreeShell d n) s).1 =
      (∏ i ∈ Finset.range (endpoint s).1.length,
        responseAttenuation (Real.tanh beta) (forwardGaussianField μ t (endpoint s) i p)) ^ 2 := by
    rw [rootPathProduct_gaussian_eq_square]
    rfl
  simp only [heq] at hs
  rw [hs]
  exact mul_comm _ _

theorem cutDescendants_empty_eq_univ (k L : ℕ) :
    cutDescendants (avoidingTreeCut (∅ : Finset (Fin d)) k) L = Finset.univ := by
  classical
  ext v
  simp

theorem measure_extensionAverage_ge_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (left : Bool) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (copies beta μ) {q | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
      extensionAverage hbeta t [] (k + 1 + L) 2 (observationCopy left q)} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  have hLaw := extensionAverage_identDistrib_gaussian (μ := μ) hbeta t left [] (k + 1 + L) 2
  have hLawSet : (copies beta μ)
      {q | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        extensionAverage hbeta t [] (k + 1 + L) 2 (observationCopy left q)} =
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      {p | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        terminalExtensionAverage hbeta [] (k + 1 + L) 2 (observation t p)} :=
    hLaw.measure_mem_eq measurableSet_Ici
  rw [hLawSet]
  have heq := terminalExtensionAverage_eq_shell_average hμ hbeta t (k + 1 + L)
  have hsets : (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      {p | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        terminalExtensionAverage hbeta [] (k + 1 + L) 2 (observation t p)} =
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      {p | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        (∑ v : TreeShell d (k + 1 + L),
          rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) p) v.1) /
            (Fintype.card (TreeShell d (k + 1 + L)) : ℝ)} := by
    exact measure_congr (heq.preimage (Set.Ici _))
  rw [hsets]
  have h := measure_gaussian_restricted_path_average_ge_le_double_exp hμ hbeta hd
    hcritical ht (∅ : Finset (Fin d)) (by simp) k L hη0 hℓ hη hηlog
      hlevel htail hlength
  simpa only [cutDescendants_empty_eq_univ, Finset.card_univ] using h

theorem integral_root_weight_mul_sq_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (left : Bool) (k L : ℕ)
    (s₀ : Extension ([] : List (Fin d)) (k + 1 + L))
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 *
      rootAttenuation hbeta t (endpoint s₀) (observationCopy left q) ^ 2 ∂copies beta μ) ≤
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) *
        (∫ q, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 ∂copies beta μ) +
      (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 *
        Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) / (2 * ((d : ℝ) - 1))) := by
  let : IsProbabilityMeasure (labelMeasure d) := by unfold labelMeasure; infer_instance
  let : IsProbabilityMeasure (observationLaw μ) := inferInstance
  let : IsProbabilityMeasure ((observationLaw μ).map (innovationMap beta)) := inferInstance
  let : IsProbabilityMeasure (copies beta μ) := by unfold copies; infer_instance
  rw [integral_root_weight_mul_extension_average hμ hbeta t left 2 s₀]
  have hw := IsingCopyStationarity.integrable_fieldDifference_sq hμ hbeta t
    (ConnectedHull.root d)
  have hmax : ∀ᵐ q ∂copies beta μ, (fieldDifference beta (ConnectedHull.root d) t q) ^ 2 ≤
      (2 * (t : ℝ) + 2 * (d : ℝ) * beta) ^ 2 := by
    filter_upwards [ae_fieldDifference_bound hμ hbeta kernel_graphLaw t
      (ConnectedHull.root d)] with q hq
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hq 2
  have hp := measure_extensionAverage_ge_le_double_exp hμ hbeta hd hcritical ht
    left k L hη0 hℓ hη hηlog hlevel htail hlength
  have hprob : (copies beta μ).real
      {q | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
        extensionAverage hbeta t [] (k + 1 + L) 2 (observationCopy left q)} ≤
      Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) / (2 * ((d : ℝ) - 1))) := by
    have hp' := (measure_mono (show
        {q | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
          extensionAverage hbeta t [] (k + 1 + L) 2 (observationCopy left q)} ⊆
        {q | Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
          extensionAverage hbeta t [] (k + 1 + L) 2 (observationCopy left q)}
        from fun (q : CopySpace d)
          (h : Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) <
            extensionAverage hbeta t [] (k + 1 + L) 2 (observationCopy left q)) =>
          (show Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
            extensionAverage hbeta t [] (k + 1 + L) 2 (observationCopy left q) from h.le))).trans hp
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hp').trans_eq
      (ENNReal.toReal_ofReal (Real.exp_pos _).le)
  exact DependentWeight.integral_mul_le_of_tail_probability hw
    ((measurable_extensionAverage hbeta t [] (k + 1 + L) 2).comp
      (measurable_observationCopy left)) (Real.exp_pos _).le (sq_nonneg _)
    (Filter.Eventually.of_forall (fun q => sq_nonneg _)) hmax
    (Filter.Eventually.of_forall (fun q =>
      (extensionAverage_mem_Icc hbeta t s₀ 2 (observationCopy left q)).1))
    (Filter.Eventually.of_forall (fun q =>
      (extensionAverage_mem_Icc hbeta t s₀ 2 (observationCopy left q)).2)) hprob

end Problem367.IsingRootDoubleExponential

end

end OAI
