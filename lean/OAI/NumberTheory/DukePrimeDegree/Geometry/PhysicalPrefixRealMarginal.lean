import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalRootMarginal

namespace OAI

/-! # The actual one-root marginal in the full prefix coordinates -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

theorem physicalPrefixMeasure_realMarginal
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) [Nonempty Q.second]
    (A : RootBox q.distinct k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ t : ℝ, rightAction x (Matrix.SpecialLinearGroup.transvection q.distinct t) = x → t = 0) :
    haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
    let σ := shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
    haveI := shiftedRootFactorPullback_finite q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
      (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    let ρ := σ.restrict (univ ×ˢ (univ ×ˢ J))
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    ∀ᵐ z ∂C.physicalPrefixMeasure q g k Q A J μ,
      (((C.physicalPrefixMeasure q g k Q A J μ).condKernel z.1).snd).map
          (Homeomorph.addRight (-z.2.2)) =
        (anchorNormalize (intrinsicRootLeaf q.distinct μ
          (q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) z))
          (Homeomorph.addRight (-z.2.2) '' J)).restrict (Homeomorph.addRight (-z.2.2) '' J) := by
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  intro σ
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  intro ρ hp
  let ν := C.physicalPrefixMeasure q g k Q A J μ
  let F := fun z : Q.first × (Q.second × ℝ) => (z.2.1.val,z.2.2)
  have hF : Measurable F := (measurable_subtype_coe.comp measurable_snd.fst).prodMk measurable_snd.snd
  have HM := conditional_map_fibers_embedding ρ Subtype.val
    (MeasurableEmbedding.subtype_coe Q.first_open.measurableSet) F hF
  have HM' : ∀ᵐ s ∂ρ.fst, ν.condKernel s.val =
      (ρ.condKernel s).map (Prod.map Subtype.val id) := by
    exact HM
  have HB : ∀ᵐ s ∂ρ.fst, (ν.condKernel s.val).snd = (ρ.condKernel s).snd := by
    filter_upwards [HM'] with s hs
    rw [hs,Measure.snd,Measure.map_map measurable_snd
      (measurable_subtype_coe.prodMap measurable_id)]
    rfl
  have HR := C.rectangle_raw_realMarginal q g k Q A R hAR hA J hJ hwindow μ hfree hp
  apply (C.fullRectangleCoordinates_isOpenEmbedding q g k Q).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [HR,ae_of_ae_map measurable_fst.aemeasurable HB] with z hz hb
  have hpoint : q.rootFiberPoint d
      (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g))
        (C.fullRectangleCoordinates q g k Q z) =
      physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z :=
    C.rectangle_includedFiberPoint q g k Q z
  change ((ν.condKernel z.1.val).snd).map (Homeomorph.addRight (-z.2.2)) = _
  rw [hb,hpoint]
  exact hz

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
