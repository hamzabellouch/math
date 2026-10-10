import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalBaseEmbedding
import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixExchangeMeasures
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootRectangleMeasures

namespace OAI

/-! # Independent physical rectangles in the full prefix coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def physicalPrefixMeasure (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) :
    Measure ((UpperRootTransverse (d+1) × T) ×
      (positiveRootGeneratedGroup (q.remaining.erase q.root) × ℝ)) :=
  ((shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict
      (univ ×ˢ (univ ×ˢ J))).map (C.fullRectangleCoordinates q g k Q)

instance physicalPrefixMeasure_finite
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (C.physicalPrefixMeasure q g k Q A J μ) := by
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  unfold physicalPrefixMeasure
  infer_instance

theorem physicalPrefixMeasure_independent
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) [Nonempty Q.second]
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    haveI : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
    let ρ := (shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict (univ ×ˢ (univ ×ˢ J))
    haveI := shiftedRootFactorPullback_finite q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
      (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
    (∀ᵐ s ∂ρ.fst, ρ.condKernel s = (ρ.condKernel s).fst.prod (ρ.condKernel s).snd) →
    let σ := C.physicalPrefixMeasure q g k Q A J μ
    ∀ᵐ s ∂σ.fst, σ.condKernel s = (σ.condKernel s).fst.prod (σ.condKernel s).snd := by
  let : StandardBorelSpace Q.second := Q.second_open.measurableSet.standardBorel
  intro ρ
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  intro hp σ
  have H := conditional_product_map_base_embedding
    (ρ.map (q.includeRootRectangle d Subtype.val)) Subtype.val
    (MeasurableEmbedding.subtype_coe Q.first_open.measurableSet)
    (q.includeRootRectangle_conditional_independent d Subtype.val measurable_subtype_coe ρ hp)
  have he : (ρ.map (q.includeRootRectangle d Subtype.val)).map (Prod.map Subtype.val id) = σ := by
    rw [Measure.map_map (measurable_subtype_coe.prodMap measurable_id)
      (q.measurable_includeRootRectangle d Subtype.val measurable_subtype_coe)]
    rfl
  simpa only [he] using H

lemma physicalPrefixMeasure_ae_rectangle
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (hJ : MeasurableSet J) (μ : Measure (X (d+1))) :
    ∀ᵐ z ∂C.physicalPrefixMeasure q g k Q A J μ,
      z.1 ∈ Q.first ∧ z.2.1 ∈ Q.second ∧ z.2.2 ∈ J := by
  apply (C.fullRectangleCoordinates_isOpenEmbedding q g k Q).measurableEmbedding.ae_map_iff.mpr
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod (MeasurableSet.univ.prod hJ))] with z hz
  exact ⟨z.1.prop,z.2.1.prop,hz.2.2⟩

def unrestrictedPrefixBasePoint (s : UpperRootTransverse (d+1) × T) : X (d+1) :=
  C.quotientParam g (s.1,(s.2,1))

omit [MeasurableSpace T] [BorelSpace T] in
lemma continuous_unrestrictedPrefixBasePoint :
    Continuous (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) :=
  (C.quotientParam_localHomeomorph g).continuous.comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))

theorem map_physicalPrefixMeasure
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) :
    (C.physicalPrefixMeasure q g k Q A J μ).map
        (q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g))) =
      μ.restrict (physicalRootParam q.distinct (C.rectangleSlice q g k Q)
        (C.rectangleTime q g k Q) '' (univ ×ˢ (univ ×ˢ J))) := by
  rw [physicalPrefixMeasure,Measure.map_map
    (q.measurable_rootFiberPoint d _ (continuous_unrestrictedPrefixBasePoint
      (q := q) (C := C) (g := g)).measurable)
    (C.fullRectangleCoordinates_isOpenEmbedding q g k Q).measurableEmbedding.measurable]
  have he : q.rootFiberPoint d (unrestrictedPrefixBasePoint (q := q) (C := C) (g := g)) ∘
      C.fullRectangleCoordinates q g k Q =
      physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) := by
    funext z
    exact C.rectangle_includedFiberPoint q g k Q z
  rw [he]
  exact C.rectangle_measure_map q g k Q A hA J hJ hwindow μ

lemma physicalPrefixMeasure_map_exchange
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1)))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hf : c.finalEntries = allPositiveRoots (d+1)) :
    (C.physicalPrefixMeasure q g k Q A J μ).map (prefixTimeExchange (T := T) q c hf) =
      C.exchangedRectangleMeasure q g k c hf Q A J μ := by
  rw [physicalPrefixMeasure,Measure.map_map (prefixTimeExchange (T := T) q c hf).measurable
    (C.fullRectangleCoordinates_isOpenEmbedding q g k Q).measurableEmbedding.measurable]
  rfl

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
