import OAI.Analysis.KadisonKastler.ProductBoundaryRoot

namespace OAI

/-! # The random-walk mean with an arbitrary probability parameter

The extra coordinate is left unchanged by the group. The construction is
natural for every nonsingular map of that coordinate, which is the property
needed when combining the two separate boundary means.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace NonsingularAction

variable {G D Y : Type*} [Group G] [MeasurableSpace D] [MeasurableSpace Y]
  {μ : Measure D} {ν : Measure Y} [SFinite μ] [SFinite ν]

def leftOnProduct (α : NonsingularAction G D μ) : NonsingularAction G (D × Y) (μ.prod ν) where
  toPerm :=
    { toFun := fun g => Equiv.prodCongr (α.toPerm g) (Equiv.refl Y)
      map_one' := by ext z <;> simp
      map_mul' g h := by ext z <;> simp }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap
    (α.quasi g) (Measure.QuasiMeasurePreserving.id ν)

@[simp]
theorem leftOnProduct_apply (α : NonsingularAction G D μ) (g : G) (z : D × Y) :
    (α.leftOnProduct (ν := ν)).toPerm g z = (α.toPerm g z.1, z.2) := rfl

end NonsingularAction

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [IsProbabilityMeasure ν]

def randomWalkParameterizedScalarMean :
    ScalarBoundaryMean ((randomWalkBoundaryAction G).leftOnProduct (ν := ν)) :=
  let P := scalarInvariantProjection (firstCoordinateShift (Y := Y) (randomWalkAdvance G))
    (firstCoordinateShift_quasi (ν := ν) randomWalkAdvance_quasi)
  let E := firstBoundaryProjection randomWalkAdvance_quasi P
  firstBoundaryScalarMean Prod.fst measurable_fst randomWalkAdvance_quasi P E
    ((randomWalkPathAction G).leftOnProduct (ν := ν))
    ((randomWalkBoundaryAction G).leftOnProduct (ν := ν))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun g z => Prod.ext (randomWalkAdvance_action G g z.1) rfl)

theorem randomWalkParameterizedScalarMean_natural
    (T : Y → Y) (hT : Measure.QuasiMeasurePreserving T ν ν)
    (F : G →ᵇ ScalarLInfinity ((randomWalkBoundaryMeasure G).prod ν)) :
    (randomWalkParameterizedScalarMean G ν).toCLM
      ((scalarInfinityPullbackL (Prod.map id T)
        (MeasureTheory.QuasiMeasurePreserving.prodMap
          (Measure.QuasiMeasurePreserving.id (randomWalkBoundaryMeasure G)) hT)).compLeftContinuousBounded G F) =
      scalarInfinityPullback (Prod.map id T)
        (MeasureTheory.QuasiMeasurePreserving.prodMap
          (Measure.QuasiMeasurePreserving.id (randomWalkBoundaryMeasure G)) hT)
        ((randomWalkParameterizedScalarMean G ν).toCLM F) := by
  let P := scalarInvariantProjection (firstCoordinateShift (Y := Y) (randomWalkAdvance G))
    (firstCoordinateShift_quasi (ν := ν) randomWalkAdvance_quasi)
  let E := firstBoundaryProjection randomWalkAdvance_quasi P
  let TA : RandomWalkPath G × Y → RandomWalkPath G × Y := Prod.map id T
  let TB : RandomWalkBoundary G × Y → RandomWalkBoundary G × Y := Prod.map id T
  have hTA : Measure.QuasiMeasurePreserving TA ((randomWalkPathLaw G).prod ν)
      ((randomWalkPathLaw G).prod ν) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id _) hT
  have hTB : Measure.QuasiMeasurePreserving TB ((randomWalkBoundaryMeasure G).prod ν)
      ((randomWalkBoundaryMeasure G).prod ν) :=
    MeasureTheory.QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id _) hT
  let J := firstBoundaryRootL (μ := randomWalkPathLaw G) (ν := ν)
    (S := randomWalkAdvance G) (Prod.fst : RandomWalkPath G → G) measurable_fst
  change E.toCLM (J
    ((scalarInfinityPullbackL TB hTB).compLeftContinuousBounded G F)) =
    scalarInfinityPullback TB hTB (E.toCLM (J F))
  calc
    _ = E.toCLM (scalarInfinityPullback TA hTA (J F)) := congrArg E.toCLM
      (firstBoundaryRootL_natural (μ := randomWalkPathLaw G) (ν := ν)
        (S := randomWalkAdvance G) Prod.fst measurable_fst TA TB hTA hTB
        (fun _ => rfl) (fun _ => rfl) F)
    _ = _ := E.natural TA TB hTA hTB (fun _ => rfl) (fun _ => rfl) (J F)

end

end KadisonKastler

end OAI
