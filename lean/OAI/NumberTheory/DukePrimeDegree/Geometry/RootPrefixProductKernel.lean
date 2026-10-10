import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingLeafProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingProjectiveEquality
import OAI.NumberTheory.PrimePackets.DisintegrationEntropy

namespace OAI

/-! # Actual box kernels recovered from the intrinsic root product

The center of a box need not be a generic point.  The formula below uses
the product at the sampled point, translates it back, and normalizes on
the actual time domain of the box.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox

variable {d : ℕ} {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    {hP : InitialRootPattern P} {c : EliminationChain P D}
    {hf : c.finalEntries = allPositiveRoots (d+1)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {C : RootPrefixCoordinates (d+1) P T} {g : G (d+1)}

/-- The intrinsic product transported from the sampled point to the
uncentered time coordinates of the box. -/
def uncenteredIntrinsicProduct (_A : RootPrefixBox C c hP hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × T) × c.Time) : Measure c.Time :=
  ((c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z)).map
    (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
      (c.remainingWordHomeomorph hP hf).symm

/-- The normalized intrinsic-product description of a box conditional. -/
def intrinsicProductConditional (A : RootPrefixBox C c hP hf g)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (z : (UpperRootTransverse (d+1) × T) × c.Time) : Measure c.Time :=
  (anchorNormalize (A.uncenteredIntrinsicProduct μ z) A.time).restrict A.time

theorem ae_conditionalKernel_eq_intrinsicProduct
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      A.conditionalKernel μ z.1 = A.intrinsicProductConditional μ z := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  filter_upwards [A.conditional_of_based_group_measure R hAR μ
      (ae_upperRoot_stabilizer_trivial d μ hA),
    ae_remainingLeaf_eq_intrinsicProduct d hP c hf C g A R hAR μ] with z hz hp
  exact hz _ hp

theorem ae_uncenteredIntrinsicProduct_mass
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ] :
    ∀ᵐ z ∂A.coordinateMeasure μ,
      A.uncenteredIntrinsicProduct μ z A.time ≠ 0 ∧
        A.uncenteredIntrinsicProduct μ z A.time ≠ ∞ := by
  have hA (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  filter_upwards [A.based_group_measure_uncenter_mass R hAR μ
      (ae_upperRoot_stabilizer_trivial d μ hA),
    ae_remainingLeaf_eq_intrinsicProduct d hP c hf C g A R hAR μ] with z hz hp
  exact hz _ hp

/-- Finite conditional entropy in an actual box is the information in its
normalized intrinsic root product.  The integral is over actual samples,
so no genericity of the chosen chart center is required. -/
theorem conditionalEntropy_eq_intrinsicProduct
    (A : RootPrefixBox C c hP hf g) (R : ℝ) (hAR : A.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
    {α : Type*} [Fintype α]
    (Q : (UpperRootTransverse (d+1) × T) × c.Time → α)
    (hQ : ∀ a, MeasurableSet {z | Q z = a}) :
    conditionalSigmaEntropy (A.coordinateMeasure μ) Q
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace (UpperRootTransverse (d+1) × T))) =
      ∫ z, observationEntropy (A.intrinsicProductConditional μ z)
        (fun t => Q (z.1,t)) ∂A.coordinateMeasure μ := by
  rw [conditionalSigmaEntropy_fst (A.coordinateMeasure μ) Q hQ]
  calc
    _ = ∫ z, observationEntropy (A.conditionalKernel μ z.1)
        (fun t => Q (z.1,t)) ∂A.coordinateMeasure μ := by
      exact integral_map measurable_fst.aemeasurable
        (measurable_fiber_observationEntropy (A.conditionalKernel μ) Q hQ).aestronglyMeasurable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [A.ae_conditionalKernel_eq_intrinsicProduct R hAR μ] with z hz
      rw [hz]

end RootPrefixBox
end DukePrimeDegree

end

end OAI
