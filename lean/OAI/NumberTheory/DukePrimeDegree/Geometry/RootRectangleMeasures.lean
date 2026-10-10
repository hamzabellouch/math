import OAI.NumberTheory.DukePrimeDegree.Geometry.RootRectangleInclusion
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootFiberReference

namespace OAI

/-! # The included independent rectangles have the actual ambient measure -/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {d : ℕ} (q : InitialRootStep (d+1)) {T : Type*} [TopologicalSpace T]
    (C : RootPrefixCoordinates (d+1) q.processed T) (g : G (d+1)) (k : Fin (d+1))

def rectangleBasePoint (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (s : Q.first) : X (d+1) :=
  C.quotientParam g (s.val.1,(s.val.2,1))

lemma continuous_rectangleBasePoint (Q : RootTransverseRectangle (C.factorPivotDomain q g k)) :
    Continuous (C.rectangleBasePoint q g k Q) :=
  (C.quotientParam_localHomeomorph g).continuous.comp
    (continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.prodMk continuous_const))

lemma rectangle_includedFiberPoint
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (z : Q.first × (Q.second × ℝ)) :
    q.rootFiberPoint d (C.rectangleBasePoint q g k Q)
        (q.includeRootRectangle d Subtype.val z) =
      physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) z := by
  change rightAction (C.quotientParam g (z.1.val.1,(z.1.val.2,1)))
    (z.2.1.val.val * Matrix.SpecialLinearGroup.transvection q.distinct z.2.2) = _
  rw [C.quotientParam_eq_action]
  change rightAction (rightAction (Quotient.mk _ ((g*z.1.val.1.val)*C.base z.1.val.2)) 1) _ = _
  rw [rightAction_one]
  exact (C.rectangle_physicalParam q g k Q z).symm

variable [MeasurableSpace T] [BorelSpace T]

theorem map_included_rectangle
    (Q : RootTransverseRectangle (C.factorPivotDomain q g k))
    (A : RootBox q.distinct k)
    (hA : A.transverse = Set.range (C.rectangleSlice q g k Q))
    (J : Set ℝ) (hJ : MeasurableSet J)
    (hwindow : ∀ w : Q.first × Q.second,
      (Homeomorph.addRight (C.rectangleTime q g k Q w)) '' J ⊆ A.time)
    (μ : Measure (X (d+1))) :
    let ρ := (shiftedRootFactorPullback q.distinct A μ
      (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q)).restrict (univ ×ˢ (univ ×ˢ J))
    (ρ.map (q.includeRootRectangle d Subtype.val)).map
        (q.rootFiberPoint d (C.rectangleBasePoint q g k Q)) =
      μ.restrict (physicalRootParam q.distinct (C.rectangleSlice q g k Q)
        (C.rectangleTime q g k Q) '' (univ ×ˢ (univ ×ˢ J))) := by
  intro ρ
  rw [Measure.map_map
    (q.measurable_rootFiberPoint d _ (C.continuous_rectangleBasePoint q g k Q).measurable)
    (q.measurable_includeRootRectangle d Subtype.val measurable_subtype_coe)]
  have he : (q.rootFiberPoint d (C.rectangleBasePoint q g k Q)) ∘
      (q.includeRootRectangle d Subtype.val) =
        physicalRootParam q.distinct (C.rectangleSlice q g k Q) (C.rectangleTime q g k Q) :=
    funext (C.rectangle_includedFiberPoint q g k Q)
  change ρ.map ((q.rootFiberPoint d (C.rectangleBasePoint q g k Q)) ∘
    (q.includeRootRectangle d Subtype.val)) = _
  rw [he]
  exact C.rectangle_measure_map q g k Q A hA J hJ hwindow μ

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
