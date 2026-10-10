import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableFutureSigma
import OAI.NumberTheory.DukePrimeDegree.Geometry.CountableRootPrefixAtoms
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixProductKernel

namespace OAI

/-! # Actual leaf entropy conditioned on a countable future

Finite time-and-label approximations identify the conditional entropy of
any finite present label with the entropy of the actual leaf kernel
restricted to its positive-mass countable future atom.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalEntropy_countableFutureFiber
    {S V Y : Type*} [MeasurableSpace S] [MeasurableSpace V]
    [StandardBorelSpace V] [Nonempty V] [MeasurableSpace Y]
    (ρ : Measure (S × V)) [IsFiniteMeasure ρ]
    {M : ℕ} {P : Y → Fin M} (hP : Measurable P)
    {Q : Y → ℕ} (hQ : Measurable Q) {T : Y → Y} (hT : Measurable T)
    {F : S × V → Y} (hF : Measurable F)
    (hpos : ∀ᵐ z ∂ρ, ρ.condKernel z.1 (countableFutureFiber T Q F z) ≠ 0) :
    conditionalSigmaEntropy ρ (P ∘ F)
      (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace S) ⊔
        MeasurableSpace.comap F (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y)))) =
      ∫ z, observationEntropy
        ((anchorNormalize (ρ.condKernel z.1) (countableFutureFiber T Q F z)).restrict
          (countableFutureFiber T Q F z)) (fun t => P (F (z.1,t))) ∂ρ := by
  rw [←transverseCountableFutureSigma_eq_sup T Q F]
  simpa only [countableFutureFiber_eq_iInter,Function.comp_def] using
    conditionalEntropy_infinite_label_restriction ρ (hP.comp hF)
      (fun m z => countableFutureCode T Q m (F z))
      (fun m => (countableFutureCode_measurable hT hQ m).comp hF)
      (transverse_countableFutureCode_monotone T Q F)
      (countableFutureCode_fibers_antitone T Q F)
      (by simpa only [countableFutureFiber_eq_iInter] using hpos)

namespace RootPrefixBox
open scoped Topology
variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {V : Type*} [TopologicalSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V]
    {C : RootPrefixCoordinates (d+1) P₀ V} {g : G (d+1)}

theorem conditionalEntropy_countableFuture_intrinsicProduct
    (B : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {M : ℕ} {P : X (d+1) → Fin M} (hP : Measurable P)
    {Q : X (d+1) → ℕ} (hQ : Measurable Q)
    {T : X (d+1) → X (d+1)} (hT : Measurable T)
    (hgood : ∀ᵐ x ∂μ, ∀ᶠ v in 𝓝 (completeRootChain (d+1)).zeroTime, ∀ k : ℕ,
      Q (T^[k] (rightAction x ((completeRootChain (d+1)).word v)))=Q (T^[k] x)) :
    let F := C.timeParam c hP₀ hf g
    conditionalSigmaEntropy (B.coordinateMeasure μ) (P ∘ F)
      (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace (UpperRootTransverse (d+1) × V)) ⊔
        MeasurableSpace.comap F (⨆ k : ℕ, observationSigma (fun y => Q (T^[k+1] y)))) =
      ∫ z, observationEntropy
        ((anchorNormalize (B.intrinsicProductConditional μ z) (countableFutureFiber T Q F z)).restrict
          (countableFutureFiber T Q F z)) (fun t => P (F (z.1,t))) ∂B.coordinateMeasure μ := by
  let F := C.timeParam c hP₀ hf g
  have hpos : ∀ᵐ z ∂B.coordinateMeasure μ,
      (B.coordinateMeasure μ).condKernel z.1 (countableFutureFiber T Q F z) ≠ 0 := by
    filter_upwards [B.ae_wholeFutureAtom_pos μ T Q hgood] with z hz
    apply ne_of_gt
    apply hz.trans_le
    apply measure_mono
    intro t ht k
    exact ht (k+1)
  have he := conditionalEntropy_countableFutureFiber (B.coordinateMeasure μ) hP hQ hT
    (C.timeParam_localHomeomorph c hP₀ hf g).continuous.measurable hpos
  refine he.trans (integral_congr_ae ?_)
  filter_upwards [B.ae_conditionalKernel_eq_intrinsicProduct R hBR μ] with z hz
  change (B.coordinateMeasure μ).condKernel z.1 = B.intrinsicProductConditional μ z at hz
  rw [hz]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
