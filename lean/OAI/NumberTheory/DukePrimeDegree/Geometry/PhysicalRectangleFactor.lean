import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalRectangleKernel
import OAI.NumberTheory.DukePrimeDegree.Geometry.SampledFactorIdentification

namespace OAI

/-! # The next-root product factor in an actual independent rectangle -/

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

theorem physicalPrefixMeasure_factor
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
    ∀ᵐ s ∂ρ.fst, ∃ w : positiveRootGeneratedGroup (q.remaining.erase q.root), ∃ t₀ : ℝ,
      s ∈ Q.first ∧ w ∈ Q.second ∧ t₀ ∈ J ∧
      ρ.condKernel s =
        ((anchorNormalize
          (((q.nextIntrinsicProduct d μ
            (q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g))
              (s,(w,t₀)))).map (q.nextConjugation d (-t₀))).map (Homeomorph.mulLeft w))
          Q.second).restrict Q.second).prod (ρ.condKernel s).snd := by
  intro ρ hp
  let b := unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)
  have hb : Measurable b := (continuous_unrestrictedPrefixBasePoint
    (q := q) (C := C) (g := g)).measurable
  have hρ : ρ.map (q.rootFiberPoint d b) ≪ μ := by
    rw [C.map_physicalPrefixMeasure q g k Q A hA J hJ.measurableSet hwindow μ]
    exact Measure.absolutelyContinuous_restrict
  have H := q.exists_translated_nextProduct_factor d μ b hb ρ hρ hp
    (fun _ => Q.second) (fun _ => Q.second_open.measurableSet)
    (fun z => z.1 ∈ Q.first ∧ z.2.1 ∈ Q.second ∧ z.2.2 ∈ J)
    (C.physicalPrefixMeasure_ae_rectangle q g k Q A J hJ.measurableSet μ)
    (physicalPrefixMeasure_ae_rootKernel (q := q) (c := c) (hf := hf)
      (C := C) (g := g) (k := k) Q A hA J hJ hwindow μ hfree m htime hIH)
  filter_upwards [H] with s hs
  obtain ⟨w,t₀,hw,hfct⟩ := hs
  exact ⟨w,t₀,hw.1,hw.2.1,hw.2.2,hfct⟩

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
