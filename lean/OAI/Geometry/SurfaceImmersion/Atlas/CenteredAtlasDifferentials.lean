import OAI.Geometry.SurfaceImmersion.Atlas.CenteredConvexPhase
import OAI.Geometry.SurfaceImmersion.Geometry.CovectorPullbackParameters

namespace OAI

/-! Centered quadratic phase covectors expressed through actual chart
transitions, with the Jacobian nondegeneracy needed for parameter selection. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma centered_phaseDerivative_comp {f : CurvePlane → CurvePlane}
    {x : CurvePlane} (hf : DifferentiableAt ℝ f x) (ell c : CurvePlane) (L : ℝ) :
    phaseDerivative (centeredConvexPhase ell L c ∘ f) x =
      pullCovector (fderiv ℝ f x) (ell+L • (f x-c)) := by
  unfold phaseDerivative
  rw [fderiv_comp x ((centeredConvexPhase_smooth ell L c).differentiable (by simp) _) hf,
    (centeredConvexPhase_hasFDerivAt ell L c (f x)).fderiv]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateTransition_det_ne (q p : M) {x : CurvePlane}
    (hx : x ∈ (coordinateTransition q p).source) :
    coordDet (fderiv ℝ (coordinateTransition q p) x) ≠ 0 := by
  let e := coordinateTransition q p
  exact coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun y hy => e.left_inv hy) hx

lemma actual_centered_phase_differential (q p : M) (ell c : CurvePlane) (L : ℝ)
    {x : CurvePlane} (hx : x ∈ (coordinateTransition q p).source) :
    phaseDerivative ((centeredConvexPhase ell L c ∘ coordinateChart q) ∘
      (coordinateChart p).symm) x =
      pullCovector (fderiv ℝ (coordinateTransition q p) x)
        (ell+L • (coordinateTransition q p x-c)) := by
  change phaseDerivative (centeredConvexPhase ell L c ∘ coordinateTransition q p) x = _
  exact centered_phaseDerivative_comp
    ((((coordinateTransition_smoothOn q p) x hx).contDiffAt
      ((coordinateTransition q p).open_source.mem_nhds hx)).differentiableAt (by simp)) ell c L

lemma actual_centered_phase_at (q p : M) (ell c : CurvePlane) (L : ℝ) {z : M}
    (hzp : z ∈ (coordinateChart p).source) (hzq : z ∈ (coordinateChart q).source) :
    phaseDerivative ((centeredConvexPhase ell L c ∘ coordinateChart q) ∘
      (coordinateChart p).symm) (coordinateChart p z) =
      pullCovector (fderiv ℝ (coordinateTransition q p) (coordinateChart p z))
        (ell+L • (coordinateChart q z-c)) := by
  rw [actual_centered_phase_differential q p ell c L (coordinateTransition_mem_chart q p hzp hzq),
    coordinateTransition_apply_chart q p hzp]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
