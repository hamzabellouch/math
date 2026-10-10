import OAI.Geometry.SurfaceImmersion.Geometry.ConstantNormBoundaryGeometry
import OAI.Geometry.SurfaceImmersion.Geometry.UniformStartingFamily

namespace OAI

/-! The global inward normal of a scaled spherical immersion satisfies
the nonvanishing and antipode exclusions for every nonzero direction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem spherical_initial_boundary_geometry {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hunit : ∀ p, ‖G p‖ = 1)
    {r : ℝ} (hr : 0 < r)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p))
    (p : M) {v : SmallModes.Base} (hv : v ≠ 0) :
    0 < realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p) ⬝ᵥ
        spaceCoordinates (-G p) ∧
      realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p) ≠ 0 ∧
      normalize (realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p)) ≠
        -spaceCoordinates (-G p) := by
  have hs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hR : ∀ y, coordinateMap (r • G) p y ⬝ᵥ coordinateMap (r • G) p y = r^2 := by
    intro y
    simp only [coordinateMap,Function.comp_apply,Pi.smul_apply,spaceCoordinates_dot]
    rw [real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,hunit,mul_one,sq_abs]
  have hn : r⁻¹ • (-coordinateMap (r • G) p (coordinateCenter p)) =
      spaceCoordinates (-G p) := by
    rw [coordinateMap_at_center,Pi.smul_apply,map_smul,map_neg,smul_neg,smul_smul,
      inv_mul_cancel₀ hr.ne',one_smul]
  have hh := constant_norm_boundary_geometry (coordinateDomain_open p)
    (coordinateMap_smoothOn hs p) hR hr (coordinateCenter_mem p)
    (coordinateMap_immersion_center hs p (hI p)) hv
  simpa only [hn] using hh

end ClosedSurfaceR4

end

end OAI
