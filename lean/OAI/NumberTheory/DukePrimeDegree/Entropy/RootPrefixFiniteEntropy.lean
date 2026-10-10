import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteLabelEntropy
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixProductKernel

namespace OAI

/-! # Finite future conditioning in actual root boxes

After recording a finite observation as well as the transverse coordinate,
the entropy is computed by the actual intrinsic product at the sampled
point, restricted and normalized on its observed fiber.
-/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P₀ : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP₀ : InitialRootPattern P₀} {c : EliminationChain P₀ D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P₀ T} {g : G (d+1)}

theorem conditionalEntropy_transverse_label_intrinsicProduct
    (A : RootPrefixBox C c hP₀ hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {M N : ℕ}
    (P : (UpperRootTransverse (d+1) × T) × c.Time → Fin M) (hP : Measurable P)
    (Q : (UpperRootTransverse (d+1) × T) × c.Time → Fin N) (hQ : Measurable Q) :
    conditionalSigmaEntropy (A.coordinateMeasure μ) P
        (MeasurableSpace.comap (fun z => (z.1,Q z))
          (inferInstance : MeasurableSpace ((UpperRootTransverse (d+1) × T) × Fin N))) =
      ∫ z, observationEntropy
        ((anchorNormalize (A.intrinsicProductConditional μ z) {t | Q (z.1,t)=Q z}).restrict
          {t | Q (z.1,t)=Q z}) (fun t => P (z.1,t)) ∂A.coordinateMeasure μ := by
  rw [conditionalEntropy_transverse_label_restriction (A.coordinateMeasure μ) hP hQ]
  apply integral_congr_ae
  filter_upwards [A.ae_conditionalKernel_eq_intrinsicProduct R hAR μ] with z hz
  change (A.coordinateMeasure μ).condKernel z.1 = A.intrinsicProductConditional μ z at hz
  rw [hz]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
