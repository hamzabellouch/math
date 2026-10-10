import OAI.Analysis.CircleDomains.Sobolev.PhysicalRoundIntegrals
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! The physical Euclidean plane and complex plane carry the same area
and length measures, and precomposition preserves differential norms. -/
open Set Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

def complexPlaneLinearIsometry : EuclideanPlane ≃ₗᵢ[ℝ] ℂ :=
  { complexPlaneCoordinates.toLinearEquiv with
    norm_map' := complexPlaneCoordinates_norm }

lemma complexPlaneLinearIsometry_apply (x : EuclideanPlane) :
    complexPlaneLinearIsometry x = complexPlaneCoordinates x := rfl

lemma physical_complex_hausdorff_preserving (d : ℝ) :
    MeasurePreserving complexPlaneCoordinates (μH[d] : Measure EuclideanPlane)
      (μH[d] : Measure ℂ) :=
  complexPlaneLinearIsometry.toIsometryEquiv.measurePreserving_hausdorffMeasure d

lemma complex_precomposition_fderiv_norm (u : EuclideanPlane → ℝ) (z : ℂ) :
    ‖fderiv ℝ (u ∘ complexPlaneCoordinates.symm) z‖ =
      ‖fderiv ℝ u (complexPlaneCoordinates.symm z)‖ := by
  rw [complexPlaneCoordinates.symm.comp_right_fderiv]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ complexPlaneLinearIsometry.symm

end CircleDomainRigidity

end

end OAI
