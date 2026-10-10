import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableConditionalInformation
import OAI.NumberTheory.DukePrimeDegree.Geometry.CountableRootPrefixAtoms
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixProductKernel

namespace OAI

/-! # Countable present information in an actual root box

The conditional probability is first computed for the genuine box
conditional kernel, then identified with the normalized intrinsic product
at the sampled point. No genericity of the chart center is required.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
/-- The scalar used to normalize a box cancels from conditional probabilities. -/
lemma normalized_restriction_real_ratio {Y : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (A B C : Set Y) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hA₀ : ν A ≠ 0) (hAtop : ν A ≠ ∞) :
    ((anchorNormalize ν A).restrict A).real B /
        ((anchorNormalize ν A).restrict A).real C =
      ν.real (B ∩ A) / ν.real (C ∩ A) := by
  rw [normalized_restriction_real ν A B hB, normalized_restriction_real ν A C hC]
  exact div_div_div_cancel_right₀ (ENNReal.toReal_ne_zero.mpr ⟨hA₀,hAtop⟩) _ _

namespace RootPrefixBox

variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

theorem conditionalInformation_countableFuture_intrinsicProduct
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v)))=Q (T^[k] x)) :
    let F := C.timeParam c hP₀ hf g
    conditionalInformation (B.coordinateMeasure μ) (Q ∘ F)
      (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) =ᵐ[B.coordinateMeasure μ]
      fun z => -Real.log
        ((B.intrinsicProductConditional μ z).real
            ({t | Q (F (z.1,t))=Q (F z)} ∩ countableFutureFiber T Q F z) /
          (B.intrinsicProductConditional μ z).real (countableFutureFiber T Q F z)) := by
  let F := C.timeParam c hP₀ hf g
  have hpos : ∀ᵐ z ∂B.coordinateMeasure μ,
      (B.coordinateMeasure μ).condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    apply ne_of_gt
    apply hz.trans_le
    apply measure_mono
    intro t ht k
    exact ht (k+1)
  have he := conditionalInformation_countablePresentFutureFiber (B.coordinateMeasure μ)
    hQ hT (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable hpos
  filter_upwards [he,B.ae_conditionalKernel_eq_intrinsicProduct R hBR μ] with z hz hk
  change (B.coordinateMeasure μ).condKernel z.1 = B.intrinsicProductConditional μ z at hk
  simpa only [hk] using hz

/-- In unnormalized coordinates only the actual masses of the two nested
future atoms remain; the arbitrary box normalization disappears. -/
theorem conditionalInformation_countableFuture_uncenteredIntrinsicProduct
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v)))=Q (T^[k] x)) :
    let F := C.timeParam c hP₀ hf g
    conditionalInformation (B.coordinateMeasure μ) (Q ∘ F)
      (⨆ m, transverseLabelSigma (fun z => countableFutureCode T Q m (F z))) =ᵐ[B.coordinateMeasure μ]
      fun z => -Real.log
        ((B.uncenteredIntrinsicProduct μ z).real
            (({t | Q (F (z.1,t))=Q (F z)} ∩ countableFutureFiber T Q F z) ∩ B.time) /
          (B.uncenteredIntrinsicProduct μ z).real (countableFutureFiber T Q F z ∩ B.time)) := by
  let F := C.timeParam c hP₀ hf g
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable
  filter_upwards [B.conditionalInformation_countableFuture_intrinsicProduct R hBR μ hQ hT hgood,
    B.ae_uncenteredIntrinsicProduct_mass R hBR μ] with z hz hm
  refine hz.trans (congrArg (-Real.log ·) ?_)
  have hfuture : MeasurableSet (countableFutureFiber T Q F z) := by
    simp only [countableFutureFiber, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_eq_fun
      (hQ.comp ((hT.iterate (k+1)).comp (hF.comp measurable_prodMk_left))) measurable_const
  have hpresent : MeasurableSet {t | Q (F (z.1,t))=Q (F z)} :=
    measurableSet_eq_fun (hQ.comp (hF.comp measurable_prodMk_left)) measurable_const
  exact normalized_restriction_real_ratio (B.uncenteredIntrinsicProduct μ z) B.time _ _
    (hpresent.inter hfuture) hfuture hm.1 hm.2

end RootPrefixBox
end DukePrimeDegree

end

end OAI
