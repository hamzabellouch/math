import OAI.Analysis.KadisonKastler.ScalarBoundaryRoot
import OAI.Analysis.KadisonKastler.ShiftBoundaryScalarAlgebra

namespace OAI

/-! # The scalar boundary mean from rooted shift averages

Selection at the root is equivariant because the root translates by left
multiplication. The positive invariant projection then descends the
averages to the invariant boundary, with the exact module and action
identities required by `ScalarBoundaryMean`.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

omit [Group G] in
theorem scalarBoundaryRootL_module
    (b : ScalarLInfinity (shiftBoundaryMeasure μ S))
    (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr (scalarBoundaryModule b F) =
      scalarInfinityMul (scalarBoundaryLiftL b) (scalarBoundaryRootL r hr F) := by
  have hm (g : G) := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityMul_ae b (F g))
  apply Lp.ext
  filter_upwards [scalarBoundaryRootL_ae r hr (scalarBoundaryModule b F),
    scalarBoundaryRootL_ae r hr F, scalarBoundaryLiftL_ae b,
    scalarInfinityMul_ae (scalarBoundaryLiftL b) (scalarBoundaryRootL r hr F),
    ae_all_iff.mpr hm] with x ha hb hc hd he
  rw [ha, hd, hc, hb]
  exact he (r x)

theorem scalarBoundaryRootL_translate (α : NonsingularAction G X μ)
    (hcomm : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x))
    (hroot : ∀ g x, r (α.toPerm g x) = g * r x)
    (g : G) (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr (scalarBoundaryTranslate (shiftBoundaryAction μ S α hcomm) g F) =
      scalarInfinityPullback (α.toPerm g⁻¹) (α.quasi g⁻¹) (scalarBoundaryRootL r hr F) := by
  let β := shiftBoundaryAction μ S α hcomm
  have hm (t : G) := (shiftBoundaryMap_measurePreserving μ S).quasiMeasurePreserving.ae
    (scalarInfinityPullback_ae (β.toPerm g⁻¹) (β.quasi g⁻¹) (F (g⁻¹ * t)))
  apply Lp.ext
  filter_upwards [scalarBoundaryRootL_ae r hr (scalarBoundaryTranslate β g F),
    scalarInfinityPullback_ae (α.toPerm g⁻¹) (α.quasi g⁻¹) (scalarBoundaryRootL r hr F),
    (α.quasi g⁻¹).ae (scalarBoundaryRootL_ae r hr F), ae_all_iff.mpr hm]
    with x ha hb hc hd
  rw [ha, hb, hc, hroot]
  exact hd (r x)

def rootedScalarBoundaryMean
    (hS : Measure.QuasiMeasurePreserving S μ μ) (P : ScalarInvariantProjection S hS)
    (α : NonsingularAction G X μ)
    (hcomm : ∀ g x, S (α.toPerm g x) = α.toPerm g (S x))
    (hroot : ∀ g x, r (α.toPerm g x) = g * r x) :
    ScalarBoundaryMean (shiftBoundaryAction μ S α hcomm) where
  toCLM := (scalarProjectionToBoundaryL P).comp (scalarBoundaryRootL r hr)
  map_one := by
    change scalarProjectionToBoundaryL P
      (scalarBoundaryRootL r hr (BoundedContinuousFunction.const G
        (scalarInfinityConst (shiftBoundaryMeasure μ S) 1))) = _
    rw [scalarBoundaryRootL_const, scalarProjectionToBoundaryL_lift]
  norm_le F := (norm_scalarProjectionToBoundaryL_le P _).trans (norm_scalarBoundaryRootL_le r hr F)
  positive F hF := by
    apply (scalarBoundaryLiftL_nonnegative_iff _).mp
    change ScalarNonnegative (scalarBoundaryLiftL
      (scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr F)))
    rw [scalarBoundaryLiftL_projection]
    exact P.positive _ (scalarBoundaryRootL_positive r hr F hF)
  module_map b F := by
    change scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr (scalarBoundaryModule b F)) =
      scalarInfinityMul b (scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr F))
    apply scalarBoundaryLiftL_injective
    rw [scalarBoundaryLiftL_projection, scalarBoundaryRootL_module,
      P.module_map _ _ (scalarBoundaryLiftL_fixed b), scalarBoundaryLiftL_mul,
      scalarBoundaryLiftL_projection]
  equivariant g F := by
    change scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr
      (scalarBoundaryTranslate (shiftBoundaryAction μ S α hcomm) g F)) =
      scalarInfinityPullback ((shiftBoundaryAction μ S α hcomm).toPerm g⁻¹)
        ((shiftBoundaryAction μ S α hcomm).quasi g⁻¹)
        (scalarProjectionToBoundaryL P (scalarBoundaryRootL r hr F))
    apply scalarBoundaryLiftL_injective
    rw [scalarBoundaryLiftL_projection, scalarBoundaryRootL_translate r hr α hcomm hroot,
      P.natural (α.toPerm g⁻¹) (α.quasi g⁻¹) (hcomm g⁻¹),
      scalarBoundaryLiftL_action, scalarBoundaryLiftL_projection]

variable (G)

/-- The original action of the countable group on its random-walk boundary
has the exact scalar mean needed by the stability argument. -/
def randomWalkScalarBoundaryMean : ScalarBoundaryMean (randomWalkBoundaryAction G) :=
  rootedScalarBoundaryMean (μ := randomWalkPathLaw G) (S := randomWalkAdvance G)
    Prod.fst measurable_fst randomWalkAdvance_quasi
    (scalarInvariantProjection (randomWalkAdvance G) randomWalkAdvance_quasi)
    (randomWalkPathAction G) (randomWalkAdvance_action G) (fun _ _ => rfl)

end

end KadisonKastler

end OAI
