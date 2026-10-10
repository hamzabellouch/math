import OAI.Probability.FreeIsing.Gaussian.CutChannels
import OAI.Probability.FreeIsing.Gaussian.InwardCutConcentration
import OAI.Probability.FreeIsing.Ising.OrientedPathWeights
import OAI.Probability.FreeIsing.Ising.RootGaussianCut
import OAI.Probability.FreeIsing.Trees.InfiniteInwardCavity

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingOrientedPath
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral IsingConditionalCopyBounds
open TreeOrbitAverage PlantedSymmetry CavityFieldLimit PathSideBranches

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

def terminalAttenuation (hb : 0 ≤ beta) (inward : Bool) (v : TreeVertex d)
    (y : TreeVertex d → ℝ) : ℝ :=
  ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
    (infiniteCavityField hb (edge inward v i).1 (edge inward v i).2 y)

theorem measurable_terminalAttenuation (hb : 0 ≤ beta) (inward : Bool)
    (v : TreeVertex d) : Measurable (terminalAttenuation hb inward v) := by
  unfold terminalAttenuation
  exact Finset.measurable_prod _ (fun i _ =>
    (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).measurable.comp
      (measurable_infiniteCavityField hb _ _))

theorem attenuation_eq_terminal (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    (v : TreeVertex d) (x : Paths d) :
    attenuation hb t inward v x = terminalAttenuation hb inward v (fun i => x i t) := rfl

def terminalExtensionAverage (hb : 0 ≤ beta) (inward : Bool)
    (stem : List (Fin d)) (n : ℕ) : (TreeVertex d → ℝ) → ℝ :=
  WeightedOrbitAverage.average (fun s : Extension stem n => fun y =>
    terminalAttenuation hb inward (endpoint s) y ^ 2)

theorem measurable_terminalExtensionAverage (hb : 0 ≤ beta) (inward : Bool)
    (stem : List (Fin d)) (n : ℕ) :
    Measurable (terminalExtensionAverage hb inward stem n) := by
  unfold terminalExtensionAverage WeightedOrbitAverage.average
  apply Measurable.const_mul
  exact Finset.measurable_sum _ (fun s _ =>
    (measurable_terminalAttenuation hb inward (endpoint s)).pow_const 2)

theorem extensionAverage_identDistrib_gaussian (hb : 0 ≤ beta) (t : ℝ≥0)
    (inward : Bool) (stem : List (Fin d)) (n : ℕ) :
    IdentDistrib (extensionAverage hb t inward stem n)
      (fun z => terminalExtensionAverage hb inward stem n (observation t z))
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hobs : HasLaw (observation (ι := TreeVertex d) t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  exact ((hasLaw_observationLaw_eval μ t).identDistrib hobs).comp
    (measurable_terminalExtensionAverage hb inward stem n)

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_inward_sq_eq_rootPathProduct
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun z => terminalAttenuation hb true v (observation t z) ^ 2) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun z => rootPathProduct (gaussianInwardConeFactor μ t (Real.tanh beta) z) v := by
  have hfield (i : Fin v.1.length) :=
    hμ.infiniteCavityField_path_eq_inward_posterior hb t v i.2
  filter_upwards [ae_all_iff.mpr hfield] with z hz
  rw [rootPathProduct_gaussianInwardConeFactor, terminalAttenuation, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  exact congrArg (fun x => responseAttenuation (Real.tanh beta) x ^ 2)
    (hz ⟨i, Finset.mem_range.mp hi⟩)

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_outward_sq_eq_rootPathProduct
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun z => terminalAttenuation hb false v (observation t z) ^ 2) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun z => rootPathProduct (gaussianConeFactor μ t (Real.tanh beta) z) v := by
  filter_upwards [IsingRootGaussianCut.terminalAttenuation_eq_forward_product hμ hb t v]
    with z hz
  change IsingRootGaussianCut.terminalAttenuation hb v (observation t z) ^ 2 = _
  rw [hz, ← Finset.prod_pow]
  rfl

def orientedGaussianFactor (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (theta : ℝ) (inward : Bool)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) : TreeVertex d → ℝ :=
  if inward then gaussianInwardConeFactor μ t theta z else gaussianConeFactor μ t theta z

omit [IsProbabilityMeasure μ] in
theorem terminalAttenuation_sq_eq_rootPathProduct
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) (v : TreeVertex d) :
    (fun z => terminalAttenuation hb inward v (observation t z) ^ 2) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun z => rootPathProduct (orientedGaussianFactor μ t (Real.tanh beta) inward z) v := by
  cases inward
  · exact terminalAttenuation_outward_sq_eq_rootPathProduct hμ hb t v
  · exact terminalAttenuation_inward_sq_eq_rootPathProduct hμ hb t v

def restrictedAverage (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    {n : ℕ} (I : Finset (TreeShell d n)) (x : Paths d) : ℝ :=
  (∑ v ∈ I, attenuation hb t inward v.1 x ^ 2) / (I.card : ℝ)

theorem measurable_restrictedAverage (hb : 0 ≤ beta) (t : ℝ≥0) (inward : Bool)
    {n : ℕ} (I : Finset (TreeShell d n)) :
    Measurable (restrictedAverage hb t inward I) := by
  unfold restrictedAverage
  exact (Finset.measurable_sum _ (fun v _ =>
    (measurable_attenuation hb t inward v.1).pow_const 2)).div_const _

theorem restrictedAverage_identDistrib_gaussian
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (inward : Bool) {n : ℕ} (I : Finset (TreeShell d n)) :
    IdentDistrib (restrictedAverage hb t inward I)
      (fun z => (∑ v ∈ I,
        rootPathProduct (orientedGaussianFactor μ t (Real.tanh beta) inward z) v.1) /
          (I.card : ℝ)) (observationLaw μ)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let F : (TreeVertex d → ℝ) → ℝ := fun y =>
    (∑ v ∈ I, terminalAttenuation hb inward v.1 y ^ 2) / (I.card : ℝ)
  have hF : Measurable F :=
    (Finset.measurable_sum _ (fun v _ =>
      (measurable_terminalAttenuation hb inward v.1).pow_const 2)).div_const _
  have hobs : HasLaw (observation (ι := TreeVertex d) t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
    ⟨(measurable_observation t).aemeasurable, rfl⟩
  have hlaw := ((hasLaw_observationLaw_eval μ t).identDistrib hobs).comp hF
  apply hlaw.trans
  apply IdentDistrib.of_ae_eq (hF.comp (measurable_observation t)).aemeasurable
  filter_upwards [ae_all_iff.mpr (fun v : TreeShell d n =>
    terminalAttenuation_sq_eq_rootPathProduct hμ hb t inward v.1)] with z hz
  change (∑ v ∈ I, terminalAttenuation hb inward v.1 (observation t z) ^ 2) /
    (I.card : ℝ) = _
  congr 1
  exact Finset.sum_congr rfl (fun v _ => hz v)

def orientationCutCost (beta : ℝ) (inward : Bool) : ℝ :=
  if inward then Real.exp (4 * beta / (1 - Real.tanh beta)) else 1

theorem measure_restrictedAverage_ge_le_double_exp
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (inward : Bool)
    (forbidden : Finset (Fin d)) (hforbidden : forbidden.card ≤ 1) (k L : ℕ)
    {η ℓ : ℝ} (hη0 : 0 ≤ η) (hℓ : 0 ≤ ℓ)
    (hη : η ≤ ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) / 4)
    (hηlog : η ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ)) (htail : ℓ / 2 ≤ (L : ℝ))
    (hlength : 8 * Real.log 2 ≤
      ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
        (min (Real.sqrt (t : ℝ)) 1 * ℓ)) :
    (observationLaw μ) {x | orientationCutCost beta inward *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ) ≤
        restrictedAverage hb t inward (cutDescendants (avoidingTreeCut forbidden k) L) x} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) /
        (2 * ((d : ℝ) - 1)))) := by
  have heq := (restrictedAverage_identDistrib_gaussian hμ hb t inward
    (cutDescendants (avoidingTreeCut forbidden k) L)).measure_mem_eq
    (measurableSet_Ici (a := orientationCutCost beta inward *
      Real.exp (-(η * min (Real.sqrt (t : ℝ)) 1) * ℓ)))
  simp only [Set.preimage, Set.mem_Ici] at heq
  rw [heq]
  cases inward
  · simpa only [orientationCutCost, orientedGaussianFactor, Bool.false_eq_true,
      ↓reduceIte, one_mul] using
      measure_gaussian_restricted_path_average_ge_le_double_exp hμ hb hd hcritical ht
        forbidden hforbidden k L hη0 hℓ hη hηlog hlevel htail hlength
  · exact measure_gaussian_inward_restricted_path_average_ge_le_double_exp
      hμ hb hd hcritical ht forbidden hforbidden k L hη0 hℓ hη hηlog hlevel htail hlength

end Problem367.IsingOrientedPath

end

end OAI
