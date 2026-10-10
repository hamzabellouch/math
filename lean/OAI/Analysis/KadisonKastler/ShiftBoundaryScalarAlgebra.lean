import OAI.Analysis.KadisonKastler.ShiftBoundaryScalarMaps

namespace OAI

/-! # Algebra and action compatibility of the invariant scalar inclusion -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X} {hS : Measure.QuasiMeasurePreserving S μ μ}

theorem scalarBoundaryLiftL_projection (P : ScalarInvariantProjection S hS)
    (f : ScalarLInfinity μ) : scalarBoundaryLiftL (scalarProjectionToBoundaryL P f) = P.toCLM f := by
  apply Lp.ext
  exact (scalarBoundaryLiftL_ae _).trans (scalarProjectionToBoundaryL_ae P f)

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_const (z : ℂ) :
    scalarBoundaryLiftL (scalarInfinityConst (shiftBoundaryMeasure μ S) z) =
      scalarInfinityConst μ z := by
  apply Lp.ext
  have hp := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityConst_ae (μ := shiftBoundaryMeasure μ S) z)
  filter_upwards [scalarBoundaryLiftL_ae (scalarInfinityConst (shiftBoundaryMeasure μ S) z),
    hp, scalarInfinityConst_ae (μ := μ) z] with x hx hp hc
  exact hx.trans (hp.trans hc.symm)

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_mul (f g : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryLiftL (scalarInfinityMul f g) =
      scalarInfinityMul (scalarBoundaryLiftL f) (scalarBoundaryLiftL g) := by
  apply Lp.ext
  have hp := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae f g)
  filter_upwards [scalarBoundaryLiftL_ae (scalarInfinityMul f g), hp,
    scalarBoundaryLiftL_ae f, scalarBoundaryLiftL_ae g,
    scalarInfinityMul_ae (scalarBoundaryLiftL f) (scalarBoundaryLiftL g)]
    with x ha hb hc hd he
  rw [ha, hb, he, hc, hd]

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_nonnegative_iff (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    ScalarNonnegative (scalarBoundaryLiftL f) ↔ ScalarNonnegative f := by
  refine ⟨?_, scalarBoundaryLiftL_positive f⟩
  intro hf
  have hm : MeasurableSet {x | f x ∈ scalarPositiveCone} :=
    scalarPositiveCone_isClosed.measurableSet.preimage (Lp.stronglyMeasurable f).measurable
  have hpre : ∀ᵐ x ∂μ, f (shiftBoundaryMap μ S x) ∈ scalarPositiveCone := by
    filter_upwards [scalarBoundaryLiftL_ae f, hf] with x hx hp
    rwa [← hx]
  have hmap := (ae_map_iff (shiftBoundaryMap_measurePreserving μ S).measurable.aemeasurable hm).mpr hpre
  change ∀ᵐ x ∂shiftBoundaryMeasure μ S, f x ∈ scalarPositiveCone
  simpa only [(shiftBoundaryMap_measurePreserving μ S).map_eq] using hmap

omit [IsProbabilityMeasure μ] in
theorem scalarBoundaryLiftL_action {G : Type*} [Group G]
    (α : NonsingularAction G X μ)
    (hcomm : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x))
    (g : G) (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryLiftL (scalarInfinityPullback
      ((shiftBoundaryAction μ S α hcomm).toPerm g)
      ((shiftBoundaryAction μ S α hcomm).quasi g) f) =
      scalarInfinityPullback (α.toPerm g) (α.quasi g) (scalarBoundaryLiftL f) := by
  apply Lp.ext
  let β := shiftBoundaryAction μ S α hcomm
  have hp := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae (β.toPerm g) (β.quasi g) f)
  filter_upwards [scalarBoundaryLiftL_ae (scalarInfinityPullback (β.toPerm g) (β.quasi g) f),
    hp, scalarInfinityPullback_ae (α.toPerm g) (α.quasi g) (scalarBoundaryLiftL f),
    (α.quasi g).ae (scalarBoundaryLiftL_ae f)] with x ha hb hc hd
  rw [ha, hb, hc, hd]
  rfl

end

end KadisonKastler

end OAI
