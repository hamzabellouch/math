import OAI.Geometry.Relativity.CKS.SchwarzschildEquality
import OAI.Geometry.Relativity.CKS.SchwarzschildHorizonExclusion
import OAI.Geometry.Relativity.CKS.SchwarzschildIntrinsicHorizonDefinitions

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff
namespace CKSSchwarzschild
open CKSBoundarySurface
universe u
variable {T : Type u} [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]

omit [IsManifold I2 ∞ T] in
lemma intrinsicCoordinateMap_derivative [IsManifold I2 ∞ T] {m : ℝ}
    (D : IntrinsicInteriorImmersion m T) (p : T) :
    mfderiv I2 𝓘(ℝ,E3) (intrinsicCoordinateMap D) p =
      (mfderiv I3 𝓘(ℝ,E3) (position m) (D.map p)).comp (mfderiv I2 I3 D.map p) := by
  exact mfderiv_comp p ((position_smooth m).mdifferentiable (by simp) _)
    (D.smooth.mdifferentiable (by simp) _)

def IntrinsicInteriorImmersion.coordinateImmersion {m : ℝ} (hm : 0 < m)
    (D : IntrinsicInteriorImmersion m T) : InteriorImmersion m T where
  map := intrinsicCoordinateMap D
  smooth := (position_smooth m).comp D.smooth
  immersion p := by
    rw [intrinsicCoordinateMap_derivative]
    exact (position_derivative_injective hm _).comp (D.immersion p)
  interior p := by
    rw [intrinsicCoordinateMap,Function.comp_apply,norm_position hm]
    have hp := (interior_iff _).mp (D.interior p)
    change 2*m < 2*m + (D.map p).1.val
    linarith
  normal := intrinsicCoordinateNormal D
  normal_unit p := D.normal_unit p
  normal_orthogonal p a := by
    rw [intrinsicCoordinateMap_derivative]
    exact D.normal_orthogonal p a

theorem no_intrinsic_closed_apparent_horizon {m : ℝ} (hm : 0 < m)
    [CompactSpace T] [Nonempty T] (D : IntrinsicInteriorImmersion m T) :
    ¬ (∀ p, intrinsicSurfaceMeanCurvature D p + intrinsicSurfaceTensorTrace D p = 0 ∨
      intrinsicSurfaceMeanCurvature D p - intrinsicSurfaceTensorTrace D p = 0) := by
  exact no_closed_apparent_horizon hm (D.coordinateImmersion hm)

theorem schwarzschild_exact_equality {m : ℝ} (hm : 0 < m) :
    SchwarzschildEqualityExample m hm ∧
    ∀ (T : Type u) [TopologicalSpace T] [ChartedSpace E2 T] [IsManifold I2 ∞ T]
      [CompactSpace T] [Nonempty T] (D : IntrinsicInteriorImmersion m T),
      ¬ (∀ p, intrinsicSurfaceMeanCurvature D p + intrinsicSurfaceTensorTrace D p = 0 ∨
        intrinsicSurfaceMeanCurvature D p - intrinsicSurfaceTensorTrace D p = 0) := by
  refine ⟨schwarzschild_equality_example hm,?_⟩
  intro T _ _ _ _ _ D
  exact no_intrinsic_closed_apparent_horizon hm D
end CKSSchwarzschild

end

end OAI
