import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixCountableInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.InfiniteFutureStationarity

namespace OAI

/-! # Local stationarity of the actual whole-future root conditional

The normalized root-product description inherits the disintegration
identity on each genuine box. If that box contains the entire future
fiber, its arbitrary box normalization can be removed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_restriction_nested {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B : Set Y) (hA : MeasurableSet A) (hAB : A ⊆ B)
    (hB₀ : ν B ≠ 0) (hBtop : ν B ≠ ∞) :
    (anchorNormalize ((anchorNormalize ν B).restrict B) A).restrict A =
      (anchorNormalize ν A).restrict A := by
  rw [anchorNormalize_restrict_comm _ hA hAB,
    anchorNormalize_twice ν A B hB₀ hBtop,
    Measure.restrict_restrict_of_subset hAB]

namespace RootPrefixBox
variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

/-- Every measurable coordinate event has its original mass after
integration against the actual intrinsic-product future conditionals. -/
theorem integral_intrinsicProduct_future_probability
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v)))=Q (T^[k] x))
    (A : Set ((UpperRootTransverse (d+1) × V) × c.Time)) (hA : MeasurableSet A) :
    let F := C.timeParam c hP₀ hf g
    let f := fun z =>
      ((anchorNormalize (B.intrinsicProductConditional μ z) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A}
    Integrable f (B.coordinateMeasure μ) ∧
      (∫ z, f z ∂B.coordinateMeasure μ) = (B.coordinateMeasure μ).real A := by
  let F := C.timeParam c hP₀ hf g
  have hpos : ∀ᵐ z ∂B.coordinateMeasure μ,
      (B.coordinateMeasure μ).condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    exact ne_of_gt (hz.trans_le (measure_mono (fun t ht k => ht (k+1))))
  have H := integral_countableFuture_conditional_probability (B.coordinateMeasure μ) hQ hT
    (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable hpos A hA
  have heq : (fun z =>
      ((anchorNormalize ((B.coordinateMeasure μ).condKernel z.1)
        (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).real
        {t | (z.1,t) ∈ A}) =ᵐ[B.coordinateMeasure μ] fun z =>
      ((anchorNormalize (B.intrinsicProductConditional μ z)
        (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).real
        {t | (z.1,t) ∈ A} := by
    filter_upwards [B.ae_conditionalKernel_eq_intrinsicProduct R hBR μ] with z hz
    change (B.coordinateMeasure μ).condKernel z.1 = B.intrinsicProductConditional μ z at hz
    rw [hz]
  exact ⟨H.1.congr heq, (integral_congr_ae heq).symm.trans H.2⟩

/-- For a box containing the entire future fiber, local stationarity
uses the unnormalized intrinsic product directly. -/
theorem integral_uncentered_wholeFuture_probability
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v)))=Q (T^[k] x))
    (hcontained : ∀ᵐ z ∂B.coordinateMeasure μ,
      countableFutureFiber T Q (C.timeParam c hP₀ hf g) z ⊆ B.time)
    (A : Set ((UpperRootTransverse (d+1) × V) × c.Time)) (hA : MeasurableSet A) :
    let F := C.timeParam c hP₀ hf g
    let f := fun z =>
      ((anchorNormalize (B.uncenteredIntrinsicProduct μ z) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A}
    Integrable f (B.coordinateMeasure μ) ∧
      (∫ z, f z ∂B.coordinateMeasure μ) = (B.coordinateMeasure μ).real A := by
  let F := C.timeParam c hP₀ hf g
  have H := B.integral_intrinsicProduct_future_probability R hBR μ hQ hT hgood A hA
  have heq : (fun z =>
      ((anchorNormalize (B.intrinsicProductConditional μ z)
        (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).real
        {t | (z.1,t) ∈ A}) =ᵐ[B.coordinateMeasure μ] fun z =>
      ((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
        (countableFutureFiber T Q F z)).restrict (countableFutureFiber T Q F z)).real
        {t | (z.1,t) ∈ A} := by
    filter_upwards [B.ae_uncenteredIntrinsicProduct_mass R hBR μ,hcontained] with z hz hc
    have hfuture : MeasurableSet (countableFutureFiber T Q F z) := by
      simp only [countableFutureFiber, Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro k
      exact measurableSet_eq_fun
        (hQ.comp ((hT.iterate (k+1)).comp
          ((C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable.comp
            measurable_prodMk_left))) measurable_const
    rw [intrinsicProductConditional,
      normalized_restriction_nested _ _ _ hfuture hc hz.1 hz.2]
  exact ⟨H.1.congr heq, (integral_congr_ae heq).symm.trans H.2⟩

/-- Restriction to a future event commutes with local disintegration.
The whole future need be inside the box only on that event. -/
theorem setIntegral_uncentered_wholeFuture_probability
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v)))=Q (T^[k] x))
    (E : Set ((UpperRootTransverse (d+1) × V) × c.Time))
    (hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (C.timeParam c hP₀ hf g z))] E)
    (hcontained : ∀ᵐ z ∂(B.coordinateMeasure μ).restrict E,
      countableFutureFiber T Q (C.timeParam c hP₀ hf g) z ⊆ B.time)
    (A : Set ((UpperRootTransverse (d+1) × V) × c.Time)) (hA : MeasurableSet A) :
    (∫ z in E,
      ((anchorNormalize (B.uncenteredIntrinsicProduct μ z)
        (countableFutureFiber T Q (C.timeParam c hP₀ hf g) z)).restrict
        (countableFutureFiber T Q (C.timeParam c hP₀ hf g) z)).real
          {t | (z.1,t) ∈ A} ∂B.coordinateMeasure μ) =
      (B.coordinateMeasure μ).real (A ∩ E) := by
  let F := C.timeParam c hP₀ hf g
  have hpos : ∀ᵐ z ∂B.coordinateMeasure μ,
      (B.coordinateMeasure μ).condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    exact ne_of_gt (hz.trans_le (measure_mono (fun t ht k => ht (k+1))))
  have H := setIntegral_countableFuture_conditional_probability
    (B.coordinateMeasure μ) hQ hT
    (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable hpos A hA E hE
  refine (integral_congr_ae ?_).trans H
  filter_upwards [ae_restrict_of_ae (B.ae_conditionalKernel_eq_intrinsicProduct R hBR μ),
    ae_restrict_of_ae (B.ae_uncenteredIntrinsicProduct_mass R hBR μ),
    hcontained] with z hz hm hc
  have hfuture : MeasurableSet (countableFutureFiber T Q F z) := by
    simp only [countableFutureFiber, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_eq_fun
      (hQ.comp ((hT.iterate (k+1)).comp
        ((C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable.comp
          measurable_prodMk_left))) measurable_const
  change (B.coordinateMeasure μ).condKernel z.1 = B.intrinsicProductConditional μ z at hz
  rw [hz, intrinsicProductConditional,
    normalized_restriction_nested _ _ _ hfuture hc hm.1 hm.2]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
