import OAI.Analysis.KadisonKastler.ProductBoundaryLifts

namespace OAI

/-! # Algebraic identities for first-coordinate boundary descent -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {S : X → X}

theorem firstBoundaryLiftL_const (z : ℂ) :
    firstBoundaryLiftL μ S (scalarInfinityConst ((shiftBoundaryMeasure μ S).prod ν) z) =
      scalarInfinityConst (μ.prod ν) z := by
  apply Lp.ext
  have hp := (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityConst_ae (μ := (shiftBoundaryMeasure μ S).prod ν) z)
  filter_upwards [firstBoundaryLiftL_ae μ S (scalarInfinityConst _ z), hp,
    scalarInfinityConst_ae (μ := μ.prod ν) z] with x hx hp hc
  exact hx.trans (hp.trans hc.symm)

theorem firstBoundaryLiftL_mul (f g : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryLiftL μ S (scalarInfinityMul f g) =
      scalarInfinityMul (firstBoundaryLiftL μ S f) (firstBoundaryLiftL μ S g) := by
  apply Lp.ext
  have hp := (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae f g)
  filter_upwards [firstBoundaryLiftL_ae μ S (scalarInfinityMul f g), hp,
    firstBoundaryLiftL_ae μ S f, firstBoundaryLiftL_ae μ S g,
    scalarInfinityMul_ae (firstBoundaryLiftL μ S f) (firstBoundaryLiftL μ S g)]
    with x ha hb hc hd he
  rw [ha, hb, he, hc, hd]

theorem firstBoundaryLiftL_nonnegative_iff
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    ScalarNonnegative (firstBoundaryLiftL μ S f) ↔ ScalarNonnegative f := by
  constructor
  · intro hf
    have hm : MeasurableSet {x | f x ∈ scalarPositiveCone} :=
      scalarPositiveCone_isClosed.measurableSet.preimage (Lp.stronglyMeasurable f).measurable
    have hpre : ∀ᵐ x ∂μ.prod ν, f (firstBoundaryMap μ S x) ∈ scalarPositiveCone := by
      filter_upwards [firstBoundaryLiftL_ae μ S f, hf] with x hx hp
      rwa [← hx]
    have hmap := (ae_map_iff (firstBoundaryMap_measurePreserving (ν := ν) μ S).measurable.aemeasurable hm).mpr hpre
    change ∀ᵐ x ∂(shiftBoundaryMeasure μ S).prod ν, f x ∈ scalarPositiveCone
    simpa only [(firstBoundaryMap_measurePreserving μ S).map_eq] using hmap
  · intro hf
    have hp := (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae hf
    filter_upwards [firstBoundaryLiftL_ae μ S f, hp] with x hx hp
    rwa [hx]

theorem firstBoundaryLiftL_fixed (hS : Measure.QuasiMeasurePreserving S μ μ)
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    scalarInfinityPullback (firstCoordinateShift S) (firstCoordinateShift_quasi hS)
      (firstBoundaryLiftL μ S f) = firstBoundaryLiftL μ S f := by
  have hm : AEStronglyMeasurable[firstInvariantSigma μ S]
      (fun z : X × Y => f (firstBoundaryMap μ S z)) (μ.prod ν) :=
    (Lp.stronglyMeasurable f).aestronglyMeasurable
  have hf := firstInvariantSigma_fixed hS hm
  apply Lp.ext
  filter_upwards [scalarInfinityPullback_ae (firstCoordinateShift S)
      (firstCoordinateShift_quasi hS) (firstBoundaryLiftL μ S f),
    firstBoundaryLiftL_ae μ S f,
    (firstCoordinateShift_quasi (ν := ν) hS).ae (firstBoundaryLiftL_ae μ S f), hf]
    with x hp hx hs hf
  exact hp.trans (hs.trans (hf.trans hx.symm))

theorem firstBoundaryLiftL_intertwine
    (T : X × Y → X × Y) (U : ShiftBoundarySpace μ S × Y → ShiftBoundarySpace μ S × Y)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod ν) (μ.prod ν))
    (hU : Measure.QuasiMeasurePreserving U ((shiftBoundaryMeasure μ S).prod ν)
      ((shiftBoundaryMeasure μ S).prod ν))
    (hcomm : ∀ z, U (firstBoundaryMap μ S z) = firstBoundaryMap μ S (T z))
    (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    firstBoundaryLiftL μ S (scalarInfinityPullback U hU f) =
      scalarInfinityPullback T hT (firstBoundaryLiftL μ S f) := by
  apply Lp.ext
  have hp := (firstBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae U hU f)
  filter_upwards [firstBoundaryLiftL_ae μ S (scalarInfinityPullback U hU f), hp,
    scalarInfinityPullback_ae T hT (firstBoundaryLiftL μ S f),
    hT.ae (firstBoundaryLiftL_ae μ S f)] with x ha hb hc hd
  rw [ha, hb, hc, hd, hcomm]

namespace FirstBoundaryProjection

variable {hS : Measure.QuasiMeasurePreserving S μ μ}
  {P : ScalarInvariantProjection (firstCoordinateShift (Y := Y) S)
    (firstCoordinateShift_quasi (ν := ν) hS)} (E : FirstBoundaryProjection hS P)

theorem norm_le (f : ScalarLInfinity (μ.prod ν)) : ‖E.toCLM f‖ ≤ ‖f‖ := by
  rw [← firstBoundaryLiftL_norm μ S, E.lift_eq]
  exact P.norm_le f

theorem positive (f : ScalarLInfinity (μ.prod ν)) (hf : ScalarNonnegative f) :
    ScalarNonnegative (E.toCLM f) := by
  rw [← firstBoundaryLiftL_nonnegative_iff, E.lift_eq]
  exact P.positive f hf

theorem lift_retract (f : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν)) :
    E.toCLM (firstBoundaryLiftL μ S f) = f := by
  apply firstBoundaryLiftL_injective μ S
  rw [E.lift_eq, P.fixed _ (firstBoundaryLiftL_fixed hS f)]

theorem map_const (z : ℂ) :
    E.toCLM (scalarInfinityConst (μ.prod ν) z) =
      scalarInfinityConst ((shiftBoundaryMeasure μ S).prod ν) z := by
  rw [← firstBoundaryLiftL_const (μ := μ) (S := S) (ν := ν) z, E.lift_retract]

theorem module_map (b : ScalarLInfinity ((shiftBoundaryMeasure μ S).prod ν))
    (f : ScalarLInfinity (μ.prod ν)) :
    E.toCLM (scalarInfinityMul (firstBoundaryLiftL μ S b) f) =
      scalarInfinityMul b (E.toCLM f) := by
  apply firstBoundaryLiftL_injective μ S
  rw [E.lift_eq, P.module_map _ _ (firstBoundaryLiftL_fixed hS b),
    firstBoundaryLiftL_mul, E.lift_eq]

theorem natural
    (T : X × Y → X × Y) (U : ShiftBoundarySpace μ S × Y → ShiftBoundarySpace μ S × Y)
    (hT : Measure.QuasiMeasurePreserving T (μ.prod ν) (μ.prod ν))
    (hU : Measure.QuasiMeasurePreserving U ((shiftBoundaryMeasure μ S).prod ν)
      ((shiftBoundaryMeasure μ S).prod ν))
    (hcomm : ∀ z, U (firstBoundaryMap μ S z) = firstBoundaryMap μ S (T z))
    (hshift : ∀ z, firstCoordinateShift S (T z) = T (firstCoordinateShift S z))
    (f : ScalarLInfinity (μ.prod ν)) :
    E.toCLM (scalarInfinityPullback T hT f) = scalarInfinityPullback U hU (E.toCLM f) := by
  apply firstBoundaryLiftL_injective μ S
  rw [E.lift_eq, P.natural T hT hshift, firstBoundaryLiftL_intertwine T U hT hU hcomm,
    E.lift_eq]

end FirstBoundaryProjection

end

end KadisonKastler

end OAI
