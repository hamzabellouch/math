import OAI.Analysis.KadisonKastler.ShiftBoundaryScalarMaps
import OAI.Analysis.KadisonKastler.ScalarSectionSelection

namespace OAI

/-! # Evaluating a boundary family at the random-walk root -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {X G : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {S : X → X}
  [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [TopologicalSpace G] [DiscreteTopology G]
  (r : X → G) (hr : Measurable r)

def scalarBoundaryRootL :
    (G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) →L[ℂ] ScalarLInfinity μ :=
  (scalarSectionSelectL r hr).comp
    ((scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G)

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_apply (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr F = scalarSectionSelect r hr
      ((scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G F) := rfl

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_ae (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr F =ᵐ[μ] fun x => F (r x) (shiftBoundaryMap μ S x) := by
  rw [scalarBoundaryRootL_apply]
  filter_upwards [scalarSectionSelect_ae r hr
    ((scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G F),
    ae_all_iff.mpr (fun g => scalarBoundaryLiftL_ae (F g))] with x hx hg
  exact hx.trans (hg (r x))

omit [DiscreteTopology G] in
theorem norm_scalarBoundaryRootL_le (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    ‖scalarBoundaryRootL r hr F‖ ≤ ‖F‖ := by
  rw [scalarBoundaryRootL_apply]
  apply (norm_scalarSectionSelect_le r hr _).trans
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro g
  rw [ContinuousLinearMap.compLeftContinuousBounded_apply, norm_scalarBoundaryLiftL]
  exact F.norm_coe_le_norm g

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_const (f : ScalarLInfinity (shiftBoundaryMeasure μ S)) :
    scalarBoundaryRootL r hr (BoundedContinuousFunction.const G f) = scalarBoundaryLiftL f := by
  rw [scalarBoundaryRootL_apply]
  have he : (scalarBoundaryLiftL (μ := μ) (S := S)).compLeftContinuousBounded G
      (BoundedContinuousFunction.const G f) =
      BoundedContinuousFunction.const G (scalarBoundaryLiftL f) := by
    ext g
    rfl
  rw [he, scalarSectionSelect_const]

omit [DiscreteTopology G] in
theorem scalarBoundaryRootL_positive (F : G →ᵇ ScalarLInfinity (shiftBoundaryMeasure μ S))
    (hF : ∀ g, ScalarNonnegative (F g)) : ScalarNonnegative (scalarBoundaryRootL r hr F) := by
  rw [scalarBoundaryRootL_apply]
  exact scalarSectionSelect_positive r hr _ (fun g => scalarBoundaryLiftL_positive (F g) (hF g))

end

end KadisonKastler

end OAI
