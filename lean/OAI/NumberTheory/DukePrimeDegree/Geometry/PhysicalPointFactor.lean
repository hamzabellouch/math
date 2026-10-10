import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalRectangleKernel
import OAI.NumberTheory.DukePrimeDegree.Geometry.FactorAtSample

namespace OAI

/-! # The remaining factor at almost every point of a physical rectangle -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

theorem physicalPrefixMeasure_factor_at_sample
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    [ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1)) μ]
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
    let ρ := C.physicalPrefixMeasure q g k Q A J μ
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    ∀ᵐ z ∂ρ, ρ.condKernel z.1 =
      ((anchorNormalize
        (((q.nextIntrinsicProduct d μ
          (q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z)).map
            (q.nextConjugation d (-z.2.2))).map (Homeomorph.mulLeft z.2.1))
        Q.second).restrict Q.second).prod (ρ.condKernel z.1).snd := by
  intro ρ hp
  have hc := physicalPrefixMeasure_ae_rootKernel (q := q) (c := c) (hf := hf)
    (C := C) (g := g) (k := k) Q A hA J hJ hwindow μ hfree m htime hIH
  have ht := q.ae_prefixRootExchange_conditional_at_sample d ρ hp
  have hprod := ae_of_ae_map measurable_fst.aemeasurable hp
  filter_upwards [hc,ht,hprod] with z hz ht hp
  exact q.factor_of_conjugated_fst d (ρ.condKernel z.1) hp _ z.2.1 z.2.2
    Q.second Q.second_open.measurableSet (ht.symm.trans hz)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
