import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTensorPullback

namespace OAI

/-! Tensor pullback cancels along the actual local phase inverse. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.JetPolynomial

lemma tensorCoordinatePullback_inverse
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : Base} (hp : p ∈ e.target) (H : PhaseMean.Tensor) :
    tensorCoordinatePullbackValue e.symm p (tensorCoordinatePullbackValue e (e.symm p) H) = H := by
  have hinv : e ∘ e.symm =ᶠ[𝓝 p] id := by
    filter_upwards [e.open_target.mem_nhds hp] with q hq
    exact e.right_inv hq
  have hchain : (fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p) =
      ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
      hinv.fderiv_eq,fderiv_id]
  have hcancel (v : SmallModes.Base) :
      tensorCoordinateDerivative e (e.symm p) (tensorCoordinateDerivative e.symm p v) = v := by
    change planeCoordinateIsometry
      ((fderiv ℝ e (e.symm p)) (planeCoordinateIsometry.symm
        (planeCoordinateIsometry ((fderiv ℝ e.symm p) (planeCoordinateIsometry.symm v))))) = v
    rw [LinearIsometryEquiv.symm_apply_apply]
    change planeCoordinateIsometry (((fderiv ℝ e (e.symm p)).comp
      (fderiv ℝ e.symm p)) (planeCoordinateIsometry.symm v)) = v
    rw [hchain,ContinuousLinearMap.id_apply,LinearIsometryEquiv.apply_symm_apply]
  funext j
  change PhaseMean.evaluate (PhaseMean.pullback (tensorCoordinateDerivative e (e.symm p)) H)
    (tensorCoordinateDerivative e.symm p (PhaseMean.firstDirection j))
    (tensorCoordinateDerivative e.symm p (PhaseMean.secondDirection j)) = H j
  rw [PhaseMean.evaluate_pullback,hcancel,hcancel]
  fin_cases j <;> simp [PhaseMean.evaluate,PhaseMean.firstDirection,PhaseMean.secondDirection,SmallModes.dx,SmallModes.dy]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
