import OAI.NumberTheory.DukePrimeDegree.Geometry.PhysicalPrefixCoordinates

namespace OAI

/-! # Actual prefix boxes obtained from physical independent rectangles -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain q.processed D)
    (hf : c.finalEntries = allPositiveRoots (d+1))
    {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def physicalPrefixBox
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (hA : A.transverse = range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time) :
    RootPrefixBox C c q.initial hf g where
  transverse := Q.first
  time := remainingFactorTime q c hf '' (Q.second ×ˢ J)
  transverse_open := Q.first_open
  time_open := (remainingFactorTime q c hf).isOpenMap _ (Q.second_open.prod hJ)
  embedding := by
    have H : Topology.IsOpenEmbedding
        ((C.originalRectangleCoordinates q c hf g k Q '' (univ ×ˢ (univ ×ˢ J))).domRestrict
          (C.timeParam c q.initial hf g)) := by
      apply openEmbedding_on_coordinate_image
        (C.originalRectangleCoordinates q c hf g k Q) (C.timeParam c q.initial hf g)
        (univ ×ˢ (univ ×ˢ J)) (C.originalRectangleCoordinates_openEmbedding q c hf g k Q)
        (C.timeParam_localHomeomorph c q.initial hf g) (isOpen_univ.prod (isOpen_univ.prod hJ))
      have he : (univ ×ˢ (univ ×ˢ J)).domRestrict
          (C.timeParam c q.initial hf g ∘ C.originalRectangleCoordinates q c hf g k Q) =
          (univ ×ˢ (univ ×ˢ J)).domRestrict
            (physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)) := by
        funext z
        exact C.originalRectangleCoordinates_param q c hf g k Q z.val
      rw [he]
      exact C.rectangle_param_isOpenEmbedding q g k Q A hA J hJ hwindow
    erw [C.originalRectangleCoordinates_image q c hf g k Q J] at H
    exact H

variable [MeasurableSpace T] [BorelSpace T]

lemma map_physicalPrefixMeasure_original
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) :
    (C.physicalPrefixMeasure q g k Q A J μ).map (physicalPrefixCoordinates (T := T) q c hf) =
      ((shiftedRootFactorPullback q.distinct A μ
        (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict
          (univ ×ˢ (univ ×ˢ J))).map (C.originalRectangleCoordinates q c hf g k Q) := by
  rw [physicalPrefixMeasure,Measure.map_map (physicalPrefixCoordinates (T := T) q c hf).measurable
    (C.fullRectangleCoordinates_isOpenEmbedding q g k Q).measurableEmbedding.measurable]
  rfl

theorem physicalPrefixBox_coordinateMeasure
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (hA : A.transverse = range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) :
    (C.physicalPrefixBox q c hf g k Q A hA J hJ hwindow).coordinateMeasure μ =
      (C.physicalPrefixMeasure q g k Q A J μ).map (physicalPrefixCoordinates (T := T) q c hf) := by
  let B := C.physicalPrefixBox q c hf g k Q A hA J hJ hwindow
  let σ := (C.physicalPrefixMeasure q g k Q A J μ).map (physicalPrefixCoordinates (T := T) q c hf)
  have hU : IsOpen B.domain := B.transverse_open.prod B.time_open
  have hs : ∀ᵐ z ∂σ, z ∈ B.domain := by
    dsimp only [σ]
    rw [map_physicalPrefixMeasure_original (q := q) (c := c) (hf := hf)]
    apply (C.originalRectangleCoordinates_openEmbedding q c hf g k Q).measurableEmbedding.ae_map_iff.mpr
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod (MeasurableSet.univ.prod hJ.measurableSet))]
      with z hz
    exact ⟨z.1.prop,(z.2.1.val,z.2.2),⟨z.2.1.prop,hz.2.2⟩,rfl⟩
  have hm : σ.map (C.timeParam c q.initial hf g) =
      μ.restrict (C.timeParam c q.initial hf g '' B.domain) := by
    dsimp only [σ]
    rw [map_physicalPrefixMeasure_original (q := q) (c := c) (hf := hf),
      Measure.map_map (C.timeParam_localHomeomorph c q.initial hf g).continuous.measurable
        (C.originalRectangleCoordinates_openEmbedding q c hf g k Q).measurableEmbedding.measurable]
    have he : C.timeParam c q.initial hf g ∘ C.originalRectangleCoordinates q c hf g k Q =
        physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) :=
      funext (C.originalRectangleCoordinates_param q c hf g k Q)
    have hi : C.timeParam c q.initial hf g '' B.domain =
        physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) ''
          (univ ×ˢ (univ ×ˢ J)) := by
      change C.timeParam c q.initial hf g ''
        (Q.first ×ˢ (remainingFactorTime q c hf '' (Q.second ×ˢ J))) = _
      rw [←C.originalRectangleCoordinates_image q c hf g k Q J,Set.image_image]
      exact congrArg (fun f => f '' (univ ×ˢ (univ ×ˢ J))) he
    rw [he,hi]
    exact C.rectangle_measure_map q g k Q A hA J hJ.measurableSet hwindow μ
  have H := B.restrict_eq_coordinateMeasure B.domain hU B.embedding subset_rfl μ σ hs hm
  rw [Measure.restrict_eq_self_of_ae_mem hs] at H
  exact H.symm

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
