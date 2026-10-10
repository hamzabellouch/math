import OAI.Probability.FreeIsing.Conditioning.ComponentInformation
import OAI.Probability.FreeIsing.Gaussian.StatisticSideSignalLoss
import OAI.Probability.FreeIsing.Posterior.Symmetry

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

def posteriorMean {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) :
    ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
  (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 ⟨[c], List.IsChain.singleton c⟩) |
    PlantedInformation.observationSigma (componentIndexVertex (c := c)) t]

theorem measurable_posteriorMean {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) : Measurable (posteriorMean μ c t) :=
  stronglyMeasurable_condExp.measurable.mono
    (PlantedInformation.observationSigma_le _ _) le_rfl

theorem posteriorMean_abs_le_one {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t), |posteriorMean μ c t p| ≤ 1 := by
  apply ae_bdd_abs_condExp_of_ae_bdd_abs
  filter_upwards [] with p
  cases h : p.1 (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) <;>
    norm_num [spinSign, h]

theorem posteriorMean_flip_ae {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (c : Fin d) (t : ℝ≥0) :
    (posteriorMean μ c t) ∘ plantedFlipEquiv (TreeVertex d) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)] -posteriorMean μ c t := by
  let := hμ.isProbabilityMeasure
  let m := PlantedInformation.observationSigma (componentIndexVertex (c := c)) t
  have hsmall : Measurable[m, m] (plantedFlipEquiv (TreeVertex d)) := by
    apply measurable_comap_iff.mpr
    have heq : (fun p i => observation t p (componentIndexVertex (c := c) i)) ∘
        plantedFlipEquiv (TreeVertex d) =
        fun p i => -observation t p (componentIndexVertex (c := c) i) := by
      funext p i
      exact congrFun (observation_flip t p) (componentIndexVertex i)
    rw [heq]
    exact (comap_measurable
      (fun p i => observation t p (componentIndexVertex (c := c) i))).neg
  have hnat := condExp_comp_measurePreserving_equiv
    (PlantedInformation.observationSigma_le (componentIndexVertex (c := c)) t)
    (plantedFlipEquiv (TreeVertex d))
    (product_measurePreserving_flip hμ.flip_invariant
      (gaussianNoiseLaw_map_neg (TreeVertex d) t)) hsmall hsmall
    (integrable_plantedSpin (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      ⟨[c], List.IsChain.singleton c⟩)
  have hodd : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      spinSign (p.1 ⟨[c], List.IsChain.singleton c⟩)) ∘ plantedFlipEquiv (TreeVertex d) =
      -(fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        spinSign (p.1 ⟨[c], List.IsChain.singleton c⟩)) := by
    funext p
    cases h : p.1 (⟨[c], List.IsChain.singleton c⟩ : TreeVertex d) <;>
      simp [plantedFlipEquiv, flipConfig, IsingSpin.flip, spinSign, h]
  rw [hodd] at hnat
  exact hnat.trans (condExp_neg _ _)

def posteriorLaw {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) : Measure ℝ :=
  (μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (posteriorMean μ c t)

theorem posteriorLaw_probability {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (c : Fin d) (t : ℝ≥0) : IsProbabilityMeasure (posteriorLaw μ c t) := by
  let := hμ.isProbabilityMeasure
  unfold posteriorLaw
  infer_instance

theorem posteriorLaw_abs_le_one {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) : ∀ᵐ q ∂posteriorLaw μ c t, |q| ≤ 1 := by
  exact (ae_map_iff (measurable_posteriorMean μ c t).aemeasurable
    (measurableSet_le measurable_id.abs measurable_const)).mpr
      (posteriorMean_abs_le_one μ c t)

theorem posteriorLaw_neg_invariant {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (c : Fin d) (t : ℝ≥0) :
    MeasurePreserving Neg.neg (posteriorLaw μ c t) (posteriorLaw μ c t) := by
  let := hμ.isProbabilityMeasure
  refine ⟨measurable_neg, ?_⟩
  exact FactorTransport.map_invariant_of_ae_equivariant
    (product_measurePreserving_flip hμ.flip_invariant
      (gaussianNoiseLaw_map_neg (TreeVertex d) t)) measurable_neg
    (measurable_posteriorMean μ c t) (posteriorMean_flip_ae hμ c t)

theorem posteriorLaw_information_lower {d : ℕ} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (hθ0 : -1 ≤ theta) (hθ1 : theta ≤ 1) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) :
    min (Real.sqrt (t : ℝ)) 1 / 5 ≤ ∫ q, q ^ 2 ∂posteriorLaw μ c t := by
  have hmap := integral_map (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (measurable_posteriorMean μ c t).aemeasurable
    (measurable_id.pow_const 2).aestronglyMeasurable
  simp only [id_eq] at hmap
  rw [posteriorLaw, hmap]
  exact hμ.component_critical_information_lower hθ0 hθ1 c hcritical ht

def lossCoefficient (theta : ℝ) : ℝ := min (sideSignalLossCoefficient theta / 5) (1 / 2)

theorem lossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < lossCoefficient theta :=
  lt_min (div_pos (sideSignalLossCoefficient_pos hθ0 hθ1) (by norm_num)) (by norm_num)

theorem lossCoefficient_le_half (theta : ℝ) : lossCoefficient theta ≤ 1 / 2 :=
  min_le_right _ _

theorem integral_tilted_posteriorLaw_attenuation_le {d : ℕ} {theta eta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1) (hη : |eta| ≤ 1) (c : Fin d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (z : ℝ) :
    (∫ q, responseAttenuation theta (z + statisticMessage theta q) ^ 2
      ∂linearSignalTilt (posteriorLaw μ c t) id (eta * theta)) ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  let := posteriorLaw_probability hμ c t
  have h := integral_tilted_statistic_attenuation_le hθ0.le hθ1 hη
    measurable_id (posteriorLaw_abs_le_one μ c t) (MeasurableEquiv.neg ℝ)
    (posteriorLaw_neg_invariant hμ c t) (Filter.Eventually.of_forall (fun _ => rfl)) z
  have hm := posteriorLaw_information_lower hμ (by linarith) hθ1.le c hcritical ht
  have hc := sideSignalLossCoefficient_pos hθ0 hθ1
  have hω : 0 ≤ min (Real.sqrt (t : ℝ)) 1 := le_min (Real.sqrt_nonneg _) zero_le_one
  have hco := mul_le_mul_of_nonneg_right
    (show lossCoefficient theta ≤ sideSignalLossCoefficient theta / 5 from min_le_left _ _) hω
  have hmul := mul_le_mul_of_nonneg_left hm hc.le
  simp only [id_eq] at h
  nlinarith

end Problem367.ComponentSignalAttenuation

end

end OAI
