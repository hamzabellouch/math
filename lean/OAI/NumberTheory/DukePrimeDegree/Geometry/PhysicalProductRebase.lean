import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPointFactor
import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixRealMarginal
import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedFactorProduct

namespace OAI

/-! # The actual product identity in a rebased physical rectangle -/

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

theorem physicalPrefixMeasure_rebased_product
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) [Nonempty Q.second]
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
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
    haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
    haveI := shiftedRootFactorPullback_finite q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
      (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    let θ := C.physicalPrefixMeasure q g k Q A J μ
    ∀ᵐ z ∂θ,
      let x := q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z
      (((θ.condKernel z.1).map q.remainingFactor).map
        (Homeomorph.mulLeft (q.remainingFactor z.2)⁻¹)) =
      (((anchorNormalize (q.nextIntrinsicProduct d μ x)
        (q.nextFactorRebase d z.2.1 z.2.2 '' Q.second)).restrict
          (q.nextFactorRebase d z.2.1 z.2.2 '' Q.second)).prod
      ((anchorNormalize (intrinsicRootLeaf q.distinct μ x)
        (Homeomorph.addRight (-z.2.2) '' J)).restrict (Homeomorph.addRight (-z.2.2) '' J))).map
          q.remainingFactor := by
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  intro σ
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  intro ρ hp θ
  have hpθ := C.physicalPrefixMeasure_independent q g k Q A J μ hp
  have Hnext := physicalPrefixMeasure_factor_at_sample (q := q) (C := C) (g := g) (k := k)
    (c := c) (hf := hf) Q A hA J hJ hwindow μ hfree m htime hIH hpθ
  have hAinv (u : LogCoordinates d) : μ.map (fun x => rightAction x (diagonalFlow u)) = μ :=
    (measurePreserving_smul (Multiplicative.ofAdd u) μ).map_eq
  have hroot : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hAinv).mono fun x hx => hx _ _ _
  have Hroot := C.physicalPrefixMeasure_realMarginal q g k Q A R hAR hA J hJ.measurableSet
    hwindow μ hroot hp
  filter_upwards [Hnext,Hroot] with z hn hr
  exact q.independent_factor_rebase d (θ.condKernel z.1) _ _ z.2.1 z.2.2
    Q.second Q.second_open.measurableSet J hn hr

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
