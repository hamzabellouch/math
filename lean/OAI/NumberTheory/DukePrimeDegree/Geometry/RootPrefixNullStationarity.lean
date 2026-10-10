import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixFutureStationarity
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixTransverseProduct
import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureMap
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureRestrictionNull

namespace OAI

/-! # Future stationarity on measurable mass-containment events

A box restriction can be removed when the transverse leaf measure of
the future outside that box vanishes. This event belongs to the future
sigma algebra; no literal containment of the full fiber is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P V} {g : G (d+1)}

theorem setIntegral_regularLeaf_wholeFuture_probability
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v))) = Q (T^[k] x))
    (E : Set ((UpperRootTransverse (d+1) × V) × c.Time))
    (hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (C.timeParam c hP hf g z))] E)
    (hnull : ∀ᵐ z ∂(B.coordinateMeasure μ).restrict E,
      B.regularLeafKernel R hBR μ hfree z.1
        (countableFutureFiber T Q (C.timeParam c hP hf g) z \ B.time) = 0)
    (A : Set ((UpperRootTransverse (d+1) × V) × c.Time)) (hA : MeasurableSet A) :
    (∫ z in E,
      ((anchorNormalize (B.regularLeafKernel R hBR μ hfree z.1)
        (countableFutureFiber T Q (C.timeParam c hP hf g) z)).restrict
        (countableFutureFiber T Q (C.timeParam c hP hf g) z)).real
          {t | (z.1,t) ∈ A} ∂B.coordinateMeasure μ) =
      (B.coordinateMeasure μ).real (A ∩ E) := by
  let F := C.timeParam c hP hf g
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hpos : ∀ᵐ z ∂B.coordinateMeasure μ,
      (B.coordinateMeasure μ).condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    exact ne_of_gt (hz.trans_le (measure_mono (fun t ht k => ht (k+1))))
  have H := setIntegral_countableFuture_conditional_probability
    (B.coordinateMeasure μ) hQ hT hF hpos A hA E hE
  have hs := ae_of_ae_map measurable_fst.aemeasurable (B.ae_leafMeasure_spec R hBR μ hfree)
  have hk := ae_of_ae_map measurable_fst.aemeasurable (B.ae_regularLeafKernel_eq R hBR μ hfree)
  refine (integral_congr_ae ?_).trans H
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_of_ae hk, hnull] with z hs hk hn
  have hfuture : MeasurableSet (countableFutureFiber T Q F z) := by
    simp only [countableFutureFiber, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_eq_fun
      (hQ.comp ((hT.iterate (k+1)).comp (hF.comp measurable_prodMk_left))) measurable_const
  have htime : MeasurableSet B.time := B.time_open.measurableSet
  have hmass : B.regularLeafKernel R hBR μ hfree z.1 B.time = 1 := by
    rw [hk]
    exact hs.2.1
  have hc : (B.coordinateMeasure μ).condKernel z.1 =
      (anchorNormalize (B.regularLeafKernel R hBR μ hfree z.1) B.time).restrict B.time := by
    change B.conditionalKernel μ z.1 = _
    rw [hk]
    simpa only [anchorNormalize, hs.2.1, inv_one, one_smul] using hs.2.2.1.symm
  rw [hc, normalized_restriction_of_null_diff _ _ _ hfuture htime
    (by rw [hmass]; exact one_ne_zero) (by rw [hmass]; exact ENNReal.one_ne_top) hn]

/-- Apply the local law directly on its canonical mass-containment
event. Its measurability and the null-outside-box premise are proved. -/
theorem setIntegral_massContained_wholeFuture_probability
    (B : RootPrefixBox C c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v))) = Q (T^[k] x))
    (A : Set ((UpperRootTransverse (d+1) × V) × c.Time)) (hA : MeasurableSet A) :
    let F := C.timeParam c hP hf g
    let κ := B.regularLeafKernel R hBR μ hfree
    let E := {z | κ z.1 (countableFutureFiber T Q F z \ B.time) = 0}
    (∫ z in E,
      ((anchorNormalize (κ z.1) (countableFutureFiber T Q F z)).restrict
        (countableFutureFiber T Q F z)).real {t | (z.1,t) ∈ A} ∂B.coordinateMeasure μ) =
      (B.coordinateMeasure μ).real (A ∩ E) := by
  let F := C.timeParam c hP hf g
  let κ := B.regularLeafKernel R hBR μ hfree
  let E := {z | κ z.1 (countableFutureFiber T Q F z \ B.time) = 0}
  have hF : Measurable F := (C.timeParam_localHomeomorph c hP hf g).continuous.measurable
  have hE : MeasurableSet[⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))] E :=
    measurableSet_future_mass_contained κ hT hQ hF B.time B.time_open.measurableSet
  have hEle : (⨆ m, transverseLabelSigma
      (fun z => countableFutureCode T Q m (F z))) ≤
        (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × V) × c.Time)) := by
    apply iSup_le
    intro m
    exact (measurable_fst.prodMk ((countableFutureCode_measurable hT hQ m).comp hF)).comap_le
  exact B.setIntegral_regularLeaf_wholeFuture_probability R hBR μ hfree hQ hT hgood E hE
    (ae_restrict_mem (hEle E hE)) A hA

end RootPrefixBox
end DukePrimeDegree

end

end OAI
