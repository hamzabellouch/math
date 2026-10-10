import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingWeightScalarBridge
import OAI.Analysis.IrrationalRotation.Sampling.ProductSamplingTestAlmostSure
import OAI.Analysis.IrrationalRotation.Product.ProductTestedExpectationSummability

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.ProductModel.SamplingWeights
open ProductSamplingPhaseMoments

theorem testedCoordinateWeight_eq_testedKernel (endpoint : Bool)
    (I : Finset ℕ) (m i : ℕ) (a b c d : ℝ) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    testedCoordinateWeight endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
      i (Ico a b) (Ico c d) s t =
    testedKernel m (decide (i ∈ I)) endpoint a b c d s t := by
  cases endpoint
  · rw [testedCoordinateWeight_first_eq_scalar I m i _ _ hs ht]
    by_cases hi : i ∈ I <;> simp [testedKernel, hi]
  · rw [testedCoordinateWeight_second_eq_scalar I m i _ _ s ht]
    by_cases hi : i ∈ I <;> simp [testedKernel, hi]

theorem testedAverage_eq_kernel_mean (endpoint : Bool)
    (I : Finset ℕ) (m i : ℕ) (a b c d : ℝ) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1,
      testedCoordinateWeight endpoint I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
        i (Ico a b) (Ico c d) s t) =
      mean (testedKernel m (decide (i ∈ I)) endpoint a b c d) s := by
  rw [← integral_unitInterval]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
  exact testedCoordinateWeight_eq_testedKernel endpoint I m i a b c d hs ht

theorem measurePreserving_finite_representatives (D : Finset ℕ) :
    MeasurePreserving (fun x : Base => fun i : D => circleRepresentative (x i))
      baseMeasure (Measure.pi (fun _ : D => unitInterval)) := by
  exact (measurePreserving_pi (fun _ : D => circleMeasure)
    (fun _ : D => unitInterval)
    (fun _ => CocycleSupport.measurePreserving_circleRepresentative)).comp
      (ProductSampling.measurePreserving_finset_restrict (fun _ : ℕ => circleMeasure) D)

theorem integral_angle_circle_eq_finite_unit
    (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (D : Finset ℕ) (G : (D → ℝ) → (D → ℝ) → ℝ)
    (hG : Measurable (Function.uncurry G)) :
    (∫ θ, ∫ x, G (D.restrict θ) (fun i => circleRepresentative (x i))
      ∂baseMeasure ∂Measure.infinitePi μ) =
    ∫ θ, ∫ x, G θ x ∂Measure.pi (fun _ : D => unitInterval)
      ∂Measure.pi (fun i : D => μ i) := by
  have hinner (θ : ℕ → ℝ) :
      (∫ x, G (D.restrict θ) (fun i => circleRepresentative (x i)) ∂baseMeasure) =
      ∫ x, G (D.restrict θ) x ∂Measure.pi (fun _ : D => unitInterval) := by
    have hm : Measurable (G (D.restrict θ)) :=
      hG.comp (measurable_const.prodMk measurable_id)
    have he := integral_map (measurePreserving_finite_representatives D).measurable.aemeasurable
      (show AEStronglyMeasurable (G (D.restrict θ))
        (baseMeasure.map (fun x : Base => fun i : D => circleRepresentative (x i))) by
        rw [(measurePreserving_finite_representatives D).map_eq]
        exact hm.aestronglyMeasurable)
    simpa only [(measurePreserving_finite_representatives D).map_eq] using he.symm
  simp_rw [hinner]
  exact integral_restrict_infinitePi μ (s := D)
    (f := fun θ => ∫ x, G θ x ∂Measure.pi (fun _ : D => unitInterval))
    hG.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

theorem testedAverageError_expected_eq (m : ℕ) (D I N : Finset ℕ)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i) (endpoint : Bool)
    (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      ((N.card : ℝ)⁻¹ * (∑ n ∈ N,
        testedProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) θ n x) -
        testedIdeal endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i => UniformIntervalPhase.lambdaLaw (S i))) =
      testedExpectedError m (fun i : D => S i) N (fun i : D => decide ((i : ℕ) ∈ I))
        endpoint (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i) := by
  let (i : ℕ) : IsProbabilityMeasure (UniformIntervalPhase.lambdaLaw (S i)) :=
    UniformIntervalPhase.lambdaLaw_probability (S i) (hS i)
  let u : D → ℝ → ℝ → ℝ := fun i =>
    testedKernel m (decide ((i : ℕ) ∈ I)) endpoint (a i) (b i) (c i) (d i)
  let G : (D → ℝ) → (D → ℝ) → ℝ := fun θ x =>
    ((N.card : ℝ)⁻¹ * (∑ n ∈ N, ∏ i : D,
      u i (x i) (Int.fract ((n : ℝ) * θ i))) - ∏ i : D, mean (u i) (x i))^2
  have hu (i : D) : Measurable (Function.uncurry (u i)) :=
    testedKernel_measurable m _ endpoint _ _ _ _
  have hG : Measurable (Function.uncurry G) := by
    have hv (n : ℕ) : Measurable (fun z : (D → ℝ) × (D → ℝ) =>
        ∏ i : D, u i (z.2 i) (Int.fract ((n : ℝ) * z.1 i))) := by
      apply Finset.measurable_prod
      intro i _
      have hx : Measurable (fun z : (D → ℝ) × (D → ℝ) => z.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      have ht : Measurable (fun z : (D → ℝ) × (D → ℝ) =>
          Int.fract ((n : ℝ) * z.1 i)) :=
        ((measurable_const_mul (n : ℝ)).comp
          ((measurable_pi_apply i).comp measurable_fst)).fract
      exact (hu i).comp (hx.prodMk ht)
    have hz : Measurable (fun z : (D → ℝ) × (D → ℝ) =>
        ∏ i : D, mean (u i) (z.2 i)) := by
      apply Finset.measurable_prod
      intro i _
      exact (measurable_mean (hu i)).comp ((measurable_pi_apply i).comp measurable_snd)
    exact ((measurable_const.mul (Finset.measurable_sum N (fun n _ => hv n))).sub hz).pow_const 2
  have hprod (θ : ℕ → ℝ) (n : ℕ) (x : Base) :
      testedProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
        (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) θ n x =
      ∏ i : D, u i (circleRepresentative (x i)) (Int.fract ((n : ℝ) * θ i)) := by
    rw [testedProduct, ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i _
    exact testedCoordinateWeight_eq_testedKernel endpoint I m i _ _ _ _
      (ProductCocycle.representative_mem_Ico (x i))
      ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hideal (x : Base) :
      testedIdeal endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
        (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) x =
      ∏ i : D, mean (u i) (circleRepresentative (x i)) := by
    rw [testedIdeal, ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro i _
    exact testedAverage_eq_kernel_mean endpoint I m i _ _ _ _
      (ProductCocycle.representative_mem_Ico (x i))
  simp_rw [hprod, hideal]
  exact integral_angle_circle_eq_finite_unit
    (fun i => UniformIntervalPhase.lambdaLaw (S i)) D G hG

theorem testedAverageError_expected_cond_eq (m : ℕ) (D I N : Finset ℕ)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i) (endpoint : Bool)
    (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      ((N.card : ℝ)⁻¹ * (∑ n ∈ N,
        testedProduct endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) θ n x) -
        testedIdeal endpoint D I ((m : ℝ)^(-(3 / 5 : ℝ))) (1 / (m : ℝ)^2)
          (fun i => Ico (a i) (b i)) (fun i => Ico (c i) (d i)) x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) =
      testedExpectedError m (fun i : D => S i) N (fun i : D => decide ((i : ℕ) ∈ I))
        endpoint (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i) := by
  have h := testedAverageError_expected_eq m D I N S hS endpoint a b c d
  simpa only [UniformIntervalPhase.lambdaLaw_eq_cond _ (hS _)] using h

theorem sourceTestedError_expected_eq (p : ProductScaleData) (N : ℕ → Finset ℕ)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i) (endpoint : Bool) (I : Finset ℕ)
    (a b c d : ℕ → ℝ) (j : ℕ) :
    (∫ θ, ∫ x,
      (sourceTestedError p N endpoint I (fun i => Ico (a i) (b i))
        (fun i => Ico (c i) (d i)) j θ x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) =
    testedExpectedError (p.m j)
      (fun i : Finset.range (p.prefixCount (j + 1)) => S i) (N j)
      (fun i => decide ((i : ℕ) ∈ I)) endpoint
      (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i) :=
  testedAverageError_expected_cond_eq (p.m j) (Finset.range (p.prefixCount (j + 1)))
    I (N j) S hS endpoint a b c d

theorem sourceTestedError_expected_le {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) {j : ℕ} (hm : 200 ≤ p.m j)
    (hN : ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hSle : ∀ i < p.prefixCount (j + 1), S i ≤ p.N j)
    (endpoint : Bool) (I : Finset ℕ) (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      (sourceTestedError p N endpoint I (fun i => Ico (a i) (b i))
        (fun i => Ico (c i) (d i)) j θ x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) ≤
    (8 * (p.m j : ℝ)^(3 / 5 : ℝ) * Real.log (p.m j))^(p.prefixCount (j + 1)) /
      ((N j).card : ℝ) +
    3 * ((p.prefixCount (j + 1) : ℝ) * (p.m j : ℝ)^(-50 : ℝ) *
      (1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
        (p.m j : ℝ)^(-50 : ℝ))^(p.prefixCount (j + 1) - 1)) := by
  rw [sourceTestedError_expected_eq p N S hS endpoint I a b c d j]
  have h := tested_expected_average_error_le (κ := Finset.range (p.prefixCount (j + 1)))
    hp hm (fun i => S i) (fun i => hS i)
    (fun i => hSle i (Finset.mem_range.mp i.property)) (N j) hN
    (fun i => decide ((i : ℕ) ∈ I)) endpoint
    (fun i => a i) (fun i => b i) (fun i => c i) (fun i => d i)
  simpa only [testedExpectedError, Fintype.card_coe, Finset.card_range] using h

theorem sourceTestedError_expected_le_common {p : ProductScaleData} (hp : ProductScaleLaws p)
    (N : ℕ → Finset ℕ) {j : ℕ} (hm : 200 ≤ p.m j)
    (hN : ProductSamplingPowersAt p j (N j))
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hSle : ∀ i < p.prefixCount (j + 1), S i ≤ p.N j)
    (endpoint : Bool) (I : Finset ℕ) (a b c d : ℕ → ℝ) :
    (∫ θ, ∫ x,
      (sourceTestedError p N endpoint I (fun i => Ico (a i) (b i))
        (fun i => Ico (c i) (d i)) j θ x)^2
      ∂baseMeasure ∂Measure.infinitePi (fun i =>
        ProbabilityTheory.cond volume (Icc (1 / S i) (2 / S i)))) ≤
    (8 * (p.m j : ℝ)^(3 / 5 : ℝ) * Real.log (p.m j))^(p.prefixCount (j + 1)) /
      ((N j).card : ℝ) +
    3 * ((p.prefixCount (j + 1) : ℝ) * (8 * (p.m j : ℝ)^(-50 : ℝ)) *
      (1 + 8 * (p.m j : ℝ)^(-6 / 5 : ℝ) +
        8 * (p.m j : ℝ)^(-50 : ℝ))^(p.prefixCount (j + 1) - 1)) := by
  apply (sourceTestedError_expected_le hp N hm hN S hS hSle endpoint I a b c d).trans
  have he : 0 ≤ (p.m j : ℝ)^(-50 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hd : 0 ≤ (p.m j : ℝ)^(-6 / 5 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he' : (p.m j : ℝ)^(-50 : ℝ) ≤ 8 * (p.m j : ℝ)^(-50 : ℝ) := by linarith
  have hb : 1 + 4 * (p.m j : ℝ)^(-6 / 5 : ℝ) + (p.m j : ℝ)^(-50 : ℝ) ≤
      1 + 8 * (p.m j : ℝ)^(-6 / 5 : ℝ) + 8 * (p.m j : ℝ)^(-50 : ℝ) := by linarith
  gcongr

end Invariant233.ProductModel.SamplingWeights

end

end OAI
