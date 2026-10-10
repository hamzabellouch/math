import OAI.Analysis.KadisonKastler.ProductBoundaryAlgebra
import OAI.Analysis.KadisonKastler.ScalarSectionSelection

namespace OAI

/-! # Root selection with a passive boundary coordinate -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X Y G : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {S : X → X} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

def firstBoundaryRootL :
    (G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) →L[ℂ]
      ScalarLInfinity (μ.prod ν) :=
  (scalarSectionSelectL (fun z : X × Y => r z.1) (hr.comp measurable_fst)).comp
    ((firstBoundaryLiftL μ S).compLeftContinuousBounded G)

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_ae
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr F =ᵐ[μ.prod ν]
      fun z => F (r z.1) (firstBoundaryMap μ S z) := by
  have h := ae_all_iff.mpr (fun g : G => firstBoundaryLiftL_ae μ S (F g))
  filter_upwards [scalarSectionSelect_ae (fun z : X × Y => r z.1)
    (hr.comp measurable_fst) ((firstBoundaryLiftL μ S).compLeftContinuousBounded G F), h]
    with z hz hg
  exact hz.trans (hg (r z.1))

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_norm_le
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    ‖firstBoundaryRootL r hr F‖ ≤ ‖F‖ := by
  have h : ∀ᵐ z ∂μ.prod ν, ‖firstBoundaryRootL r hr F z‖ ≤ ‖F‖ := by
    have hb := ae_all_iff.mpr (fun g : G =>
      (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae (scalarInfinity_ae_norm_le (F g)))
    filter_upwards [firstBoundaryRootL_ae r hr F, hb] with z hz hg
    rw [hz]
    exact (hg (r z.1)).trans (F.norm_coe_le_norm _)
  simpa using Lp.norm_le_of_ae_bound (norm_nonneg F) h

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_const
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr (BoundedContinuousFunction.const G f) = firstBoundaryLiftL μ S f := by
  exact Lp.ext ((firstBoundaryRootL_ae r hr _).trans (firstBoundaryLiftL_ae μ S f).symm)

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_positive
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν))
    (hF : ∀ g, ScalarNonnegative (F g)) : ScalarNonnegative (firstBoundaryRootL r hr F) := by
  have hp := ae_all_iff.mpr (fun g : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae (hF g))
  filter_upwards [firstBoundaryRootL_ae r hr F, hp] with z hz hp
  rw [hz]
  exact hp (r z.1)

omit [Group G] in
theorem firstBoundaryRootL_module
    (b : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν))
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr (scalarBoundaryModule b F) =
      scalarInfinityMul (firstBoundaryLiftL μ S b) (firstBoundaryRootL r hr F) := by
  have hm := ae_all_iff.mpr (fun g : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae (scalarInfinityMul_ae b (F g)))
  apply Lp.ext
  filter_upwards [firstBoundaryRootL_ae r hr (scalarBoundaryModule b F),
    firstBoundaryRootL_ae r hr F, firstBoundaryLiftL_ae μ S b,
    scalarInfinityMul_ae (firstBoundaryLiftL μ S b) (firstBoundaryRootL r hr F), hm]
    with z ha hb hc hd he
  rw [ha, hd, hc, hb]
  exact he (r z.1)

theorem firstBoundaryRootL_translate
    (α : NonsingularAction G (X × Y) (μ.prod ν))
    (β : NonsingularAction G (ShiftBoundarySpace μ S × Y) ((shiftBoundaryMeasure μ S).prod ν))
    (hq : ∀ g z, β.toPerm g (firstBoundaryMap μ S z) = firstBoundaryMap μ S (α.toPerm g z))
    (hroot : ∀ g z, r (α.toPerm g z).1 = g * r z.1)
    (g : G) (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr (scalarBoundaryTranslate β g F) =
      scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (firstBoundaryRootL r hr F) := by
  have hm := ae_all_iff.mpr (fun t : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae
      (scalarInfinityPullback_ae (β.toPerm g⁻¹) (β.quasi g⁻¹) (F (g⁻¹ * t))))
  apply Lp.ext
  filter_upwards [firstBoundaryRootL_ae r hr (scalarBoundaryTranslate β g F),
    scalarInfinityPullback_ae (α.toPerm g⁻¹) (α.quasi g⁻¹) (firstBoundaryRootL r hr F),
    (α.quasi g⁻¹).ae (firstBoundaryRootL_ae r hr F), hm] with z ha hb hc hd
  rw [ha, hb, hc, hroot]
  exact (hd (r z.1)).trans (congrArg (F (g⁻¹ * r z.1)) (hq g⁻¹ z))

omit [Group G] [DiscreteTopology G] in
theorem firstBoundaryRootL_natural
    (T : X × Y → X × Y) (U : ShiftBoundarySpace μ S × Y → ShiftBoundarySpace μ S × Y)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod ν) (μ.prod ν))
    (hU : Measure.QuasiMeasurePreserving U ((shiftBoundaryMeasure μ S).prod ν)
      ((shiftBoundaryMeasure μ S).prod ν))
    (hq : ∀ z, U (firstBoundaryMap μ S z) = firstBoundaryMap μ S (T z))
    (hrT : ∀ z, r (T z).1 = r z.1)
    (F : G →ᵇ ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryRootL r hr ((scalarInfinityPullbackL U hU).compLeftContinuousBounded G F) =
      scalarInfinityPullback T hT (firstBoundaryRootL r hr F) := by
  have hm := ae_all_iff.mpr (fun t : G =>
    (firstBoundaryMap_measurePreserving (ν := ν) μ S).quasiMeasurePreserving.ae
      (scalarInfinityPullback_ae U hU (F t)))
  apply Lp.ext
  filter_upwards [firstBoundaryRootL_ae r hr
      ((scalarInfinityPullbackL U hU).compLeftContinuousBounded G F),
    scalarInfinityPullback_ae T hT (firstBoundaryRootL r hr F),
    hT.ae (firstBoundaryRootL_ae r hr F), hm] with z ha hb hc hd
  rw [ha, hb, hc, hrT]
  exact (hd (r z.1)).trans (congrArg (F (r z.1)) (hq z))

def firstBoundaryScalarMean
    (hS : Measure.QuasiMeasurePreserving S μ μ)
    (P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
      (firstCoordinateShift_quasi (ν := ν) hS))
    (E : FirstBoundaryProjection (ν := ν) hS P)
    (α : NonsingularAction G (X × Y) (μ.prod ν))
    (β : NonsingularAction G (ShiftBoundarySpace μ S × Y) ((shiftBoundaryMeasure μ S).prod ν))
    (hq : ∀ g z, β.toPerm g (firstBoundaryMap μ S z) = firstBoundaryMap μ S (α.toPerm g z))
    (hroot : ∀ g z, r (α.toPerm g z).1 = g * r z.1)
    (hshift : ∀ g z, firstCoordinateShift S (α.toPerm g z) = α.toPerm g (firstCoordinateShift S z)) :
    ScalarBoundaryMean β where
  toCLM := E.toCLM.comp (firstBoundaryRootL r hr)
  map_one := by
    change E.toCLM (firstBoundaryRootL r hr (BoundedContinuousFunction.const G _)) = _
    rw [firstBoundaryRootL_const, E.lift_retract]
  norm_le F := (E.norm_le _).trans (firstBoundaryRootL_norm_le r hr F)
  positive F hF := E.positive _ (firstBoundaryRootL_positive r hr F hF)
  module_map b F := by
    change E.toCLM (firstBoundaryRootL r hr (scalarBoundaryModule b F)) = _
    rw [firstBoundaryRootL_module, E.module_map]
    rfl
  equivariant g F := by
    change E.toCLM (firstBoundaryRootL r hr (scalarBoundaryTranslate β g F)) = _
    rw [firstBoundaryRootL_translate r hr α β hq hroot,
      E.natural (α.toPerm g⁻¹) (β.toPerm g⁻¹) (α.quasi g⁻¹) (β.quasi g⁻¹)
        (hq g⁻¹) (hshift g⁻¹)]
    rfl

end

end KadisonKastler

end OAI
