import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixMeasure
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixRectangleCandidates

namespace OAI

/-! # The physical rectangle kernel in the remaining root coordinates -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1))

lemma rootKernel_of_timeKernel
    (κ ν : Measure (positiveRootGeneratedGroup (q.remaining.erase q.root)))
    (w : positiveRootGeneratedGroup (q.remaining.erase q.root)) (t : ℝ)
    (V : Set (positiveRootGeneratedGroup (q.remaining.erase q.root))) (hV : MeasurableSet V)
    (hκ : κ.map (nextTimeCoordinates q c hf) =
      (anchorNormalize
        (((ν.map q.nextGroupCast).map
          (Homeomorph.mulLeft (q.nextGroupCast (q.nextConjugation d t w)))).map
            (c.remainingWordHomeomorph q.next_initial hf).symm)
        (nextTimeFiber q c hf t '' V)).restrict (nextTimeFiber q c hf t '' V)) :
    κ = (anchorNormalize (ν.map (Homeomorph.mulLeft (q.nextConjugation d t w)))
      ((q.nextConjugation d t) '' V)).restrict ((q.nextConjugation d t) '' V) := by
  apply (nextTimeCoordinates q c hf).measurableEmbedding.map_injective
  have hCV : MeasurableSet ((q.nextConjugation d t) '' V) :=
    (q.nextConjugationHomeomorph d t).measurableEmbedding.measurableSet_image.mpr hV
  rw [normalized_nextProduct_time_coordinates q c hf _ _ hCV]
  rw [translated_nextProduct_time_coordinates q c hf] at hκ
  have hi : nextTimeCoordinates q c hf '' ((q.nextConjugation d t) '' V) =
      nextTimeFiber q c hf t '' V := by
    rw [Set.image_image]
    rfl
  simpa only [hi] using hκ

variable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] in
lemma prefixTimeExchange_fiberPoint
    (z : (UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :
    (C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hf g
      (prefixTimeExchange (T := T) q c hf z) =
      q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z := by
  rw [C.prefixTimeExchange_param, C.extendedRootParam_eq_action]
  change _ = rightAction (C.quotientParam g (z.1.1,(z.1.2,1))) _
  rw [C.quotientParam_eq_action]
  change _ = rightAction (rightAction (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) 1) _
  rw [rightAction_one]
  rfl

theorem physicalPrefixMeasure_ae_rootKernel
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
    ∀ᵐ z ∂ρ, (ρ.map (q.prefixRootExchange d)).condKernel (z.1,z.2.2) =
      (anchorNormalize
        ((q.nextIntrinsicProduct d μ
          (q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z)).map
            (Homeomorph.mulLeft (q.nextConjugation d z.2.2 z.2.1)))
        ((q.nextConjugation d z.2.2) '' Q.second)).restrict
          ((q.nextConjugation d z.2.2) '' Q.second) := by
  intro ρ
  let b := unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)
  have hb : Measurable b := (continuous_unrestrictedPrefixBasePoint
    (q := q) (C := C) (g := g)).measurable
  have hρ : ρ.map (q.rootFiberPoint d b) ≪ μ := by
    rw [C.map_physicalPrefixMeasure q g k Q A hA J hJ.measurableSet hwindow μ]
    exact Measure.absolutelyContinuous_restrict
  have hCand := ae_of_ae_map (q.measurable_rootFiberPoint d b hb).aemeasurable
    (hρ.ae_le (C.rectangle_ae_kernel_of_intrinsic_boxes q g k c hf Q A hA J hJ
      hwindow μ hfree m htime hIH))
  have hChain := ae_of_ae_map (q.measurable_rootFiberPoint d b hb).aemeasurable
    (hρ.ae_le (q.ae_nextIntrinsicProduct_chain d c hf μ))
  have he : ρ.map (prefixTimeExchange (T := T) q c hf) =
      C.exchangedRectangleMeasure q g k c hf Q A J μ :=
    C.physicalPrefixMeasure_map_exchange q g k Q A J μ c hf
  have H : ∀ᵐ a ∂(ρ.map (q.prefixRootExchange d)).fst,
      (C.exchangedRectangleMeasure q g k c hf Q A J μ).condKernel
          (Homeomorph.prodAssoc (UpperRootTransverse (d+1)) T ℝ a) =
        ((ρ.map (q.prefixRootExchange d)).condKernel a).map (nextTimeCoordinates q c hf) := by
    simpa only [he] using prefixTimeExchange_conditional q c hf ρ
  have H' := ae_of_ae_map measurable_fst.aemeasurable H
  have hTransport := ae_of_ae_map (q.measurable_prefixRootExchange d).aemeasurable H'
  filter_upwards [hCand,hChain,hTransport,
    C.physicalPrefixMeasure_ae_rectangle q g k Q A J hJ.measurableSet μ]
    with z hz hc ht hzQ
  have hzU : prefixTimeExchange (T := T) q c hf z ∈
      C.exchangedRectangleRegion q g k c hf Q J := by
    apply (exchangedRectangleRegion_mem
      (q := q) (c := c) (hf := hf) (C := C) (g := g) (k := k) Q J _).mpr
    exact ⟨hzQ.1,hzQ.2.2,z.2.1,hzQ.2.1,rfl⟩
  have hK := hz (prefixTimeExchange (T := T) q c hf z) hzU
    (prefixTimeExchange_fiberPoint (q := q) (c := c) (hf := hf) (C := C) (g := g) z)
  have hw : c.remainingWordHomeomorph q.next_initial hf
      (prefixTimeExchange (T := T) q c hf z).2 =
        q.nextGroupCast (q.nextConjugation d z.2.2 z.2.1) :=
    Homeomorph.apply_symm_apply _ _
  rw [←hc,hw,exchangedRectangleRegion_fiber
    (q := q) (c := c) (hf := hf) (C := C) (g := g) (k := k) Q J _ hzQ.1 hzQ.2.2] at hK
  exact rootKernel_of_timeKernel q c hf _ _ z.2.1 z.2.2 Q.second
    Q.second_open.measurableSet (ht.symm.trans hK)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
