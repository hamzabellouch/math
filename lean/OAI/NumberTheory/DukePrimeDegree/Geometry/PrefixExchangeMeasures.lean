import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixExchangeRegions
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixLocalRestriction

namespace OAI

/-! # Actual prefix-box measures inside an exchanged independent rectangle -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*}
    [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))
    {D : Finset (Fin (d+1))} (c : EliminationChain (insert q.root q.processed) D)
    (hfinal : c.finalEntries = allPositiveRoots (d+1))

def exchangedRectangleMeasure
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) :
    Measure ((UpperRootTransverse (d+1) × (T × ℝ)) × c.Time) :=
  ((shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict (univ ×ˢ (univ ×ˢ J))).map
      (C.exchangedRectangleCoordinates q g k c hfinal Q)

instance exchangedRectangleMeasure_finite
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (μ : Measure (X (d+1))) [IsFiniteMeasure μ] :
    IsFiniteMeasure (C.exchangedRectangleMeasure q g k c hfinal Q A J μ) := by
  let := shiftedRootFactorPullback_finite q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleSlice_isOpenEmbedding q g k Q).measurableEmbedding
    (C.rectangleTime q g k Q) (C.continuous_rectangleTime q g k Q).measurable
  unfold exchangedRectangleMeasure
  infer_instance

lemma exchangedRectangleMeasure_ae_region
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k) (J : Set ℝ) (hJ : MeasurableSet J) (μ : Measure (X (d+1))) :
    ∀ᵐ z ∂C.exchangedRectangleMeasure q g k c hfinal Q A J μ,
      z ∈ C.exchangedRectangleRegion q g k c hfinal Q J := by
  apply ((C.exchangedRectangleCoordinates_isOpenEmbedding q g k c hfinal Q).measurableEmbedding.ae_map_iff).mpr
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod (MeasurableSet.univ.prod hJ))] with z hz
  exact ⟨z,hz,rfl⟩

lemma map_exchangedRectangleMeasure
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) :
    (C.exchangedRectangleMeasure q g k c hfinal Q A J μ).map
        ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g) =
      μ.restrict ((C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g ''
        C.exchangedRectangleRegion q g k c hfinal Q J) := by
  let f := (C.extend q.initial q.root q.mem_remaining q.least).timeParam c q.next_initial hfinal g
  let θ := physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)
  have he : f ∘ C.exchangedRectangleCoordinates q g k c hfinal Q = θ :=
    funext (C.exchangedRectangleCoordinates_param q g k c hfinal Q)
  have hi : f '' C.exchangedRectangleRegion q g k c hfinal Q J = θ '' (univ ×ˢ (univ ×ˢ J)) := by
    rw [exchangedRectangleRegion,Set.image_image]
    exact congrArg (fun F => F '' (univ ×ˢ (univ ×ˢ J))) he
  change (C.exchangedRectangleMeasure q g k c hfinal Q A J μ).map f = _
  rw [hi,exchangedRectangleMeasure,Measure.map_map
    ((C.extend q.initial q.root q.mem_remaining q.least).timeParam_localHomeomorph
      c q.next_initial hfinal g).continuous.measurable
    (C.exchangedRectangleCoordinates_isOpenEmbedding q g k c hfinal Q).measurableEmbedding.measurable]
  change ((shiftedRootFactorPullback q.distinct A μ
    (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict (univ ×ˢ (univ ×ˢ J))).map
      (f ∘ C.exchangedRectangleCoordinates q g k c hfinal Q) = _
  rw [he]
  exact C.rectangle_measure_map q g k Q A hA J hJ hwindow μ

theorem exchangedRectangleMeasure_restrict_box
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1)))
    (B : RootPrefixBox (C.extend q.initial q.root q.mem_remaining q.least) c q.next_initial hfinal g)
    (hB : B.domain ⊆ C.exchangedRectangleRegion q g k c hfinal Q J) :
    (C.exchangedRectangleMeasure q g k c hfinal Q A J μ).restrict B.domain = B.coordinateMeasure μ :=
  B.restrict_eq_coordinateMeasure _
    (C.exchangedRectangleRegion_open q g k c hfinal Q J hJ)
    (C.exchangedRectangleRegion_embedding q g k c hfinal Q A hA J hJ hwindow) hB μ _
    (C.exchangedRectangleMeasure_ae_region q g k c hfinal Q A J hJ.measurableSet μ)
    (C.map_exchangedRectangleMeasure q g k c hfinal Q A hA J hJ.measurableSet hwindow μ)

theorem exchangedRectangleMeasure_restrict_overlap
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : IsOpen J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1)))
    (B : RootPrefixBox (C.extend q.initial q.root q.mem_remaining q.least) c q.next_initial hfinal g) :
    (C.exchangedRectangleMeasure q g k c hfinal Q A J μ).restrict B.domain =
      (B.coordinateMeasure μ).restrict (C.exchangedRectangleRegion q g k c hfinal Q J) :=
  B.restrict_box_eq_coordinateMeasure_restrict _
    (C.exchangedRectangleRegion_open q g k c hfinal Q J hJ)
    (C.exchangedRectangleRegion_embedding q g k c hfinal Q A hA J hJ hwindow) μ _
    (C.exchangedRectangleMeasure_ae_region q g k c hfinal Q A J hJ.measurableSet μ)
    (C.map_exchangedRectangleMeasure q g k c hfinal Q A hA J hJ.measurableSet hwindow μ)

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
