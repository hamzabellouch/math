import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixIntrinsicCandidates
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixRegionFibers
import OAI.NumberTheory.DukePrimeDegree.Geometry.NextProductTranslations

namespace OAI

/-! # Intrinsic candidates for the actual exchanged-rectangle kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

theorem rectangle_ae_kernel_of_intrinsic_boxes
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots (d+1)),
      rightAction x v = x → v = 1)
    (m : ℕ) (htime : ∀ z ∈ C.exchangedRectangleRegion q g k c hf Q J,
      z.2 ∈ c.remainingWindow 1 m)
    (hIH : ∀ B ∈ (C.extend q.initial q.root q.mem_remaining q.least).longBoxFamily
        c q.next_initial hf g 1 m,
      ∀ᵐ z ∂B.coordinateMeasure μ,
        c.remainingGroupLeafMeasure q.next_initial hf (B.basedLeaf (1+m) μ z) =
          c.remainingIntrinsicProduct q.next_initial hf μ
            ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hf g z)) :
    ∀ᵐ x ∂μ, ∀ z ∈ C.exchangedRectangleRegion q g k c hf Q J,
      (C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hf g z = x →
      (C.exchangedRectangleMeasure q g k c hf Q A J μ).condKernel z.1 =
        (anchorNormalize
          (((c.remainingIntrinsicProduct q.next_initial hf μ x).map
            (Homeomorph.mulLeft (c.remainingWordHomeomorph q.next_initial hf z.2))).map
              (c.remainingWordHomeomorph q.next_initial hf).symm)
          (Prod.mk z.1 ⁻¹' C.exchangedRectangleRegion q g k c hf Q J)).restrict
            (Prod.mk z.1 ⁻¹' C.exchangedRectangleRegion q g k c hf Q J) := by
  apply (C.extend q.initial q.root q.mem_remaining q.least).ae_region_kernel_of_intrinsic_boxes
    c q.next_initial hf g μ hfree (C.exchangedRectangleMeasure q g k c hf Q A J μ)
    (C.exchangedRectangleRegion q g k c hf Q J)
    (C.exchangedRectangleRegion_open q g k c hf Q J hJ)
    (C.exchangedRectangleRegion_embedding q g k c hf Q A hA J hJ hwindow)
    (C.exchangedRectangleMeasure_ae_region q g k c hf Q A J hJ.measurableSet μ)
    (C.map_exchangedRectangleMeasure q g k c hf Q A hA J hJ.measurableSet hwindow μ)
    m htime hIH

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
