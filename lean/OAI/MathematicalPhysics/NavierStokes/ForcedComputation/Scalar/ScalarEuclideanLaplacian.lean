import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarTransportBounds
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput

namespace OAI

/-! The scalar PDE's coordinate Laplacian equals the trace computed in
Euclidean coordinates. Thus the detector Hessian estimates have no hidden
change-of-norm factor. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian
open scoped ContDiff BigOperators

def scalarEuclidean (g : Plane → ℝ) : EuclideanPlane → ℝ := g ∘ planeCoordinates

theorem scalarEuclidean_smooth {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (scalarEuclidean g) := hg.comp planeCoordinates.contDiff

theorem scalarEuclidean_second {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (x v w : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (scalarEuclidean g)) x v w =
      fderiv ℝ (fderiv ℝ g) (planeCoordinates x) (planeCoordinates v) (planeCoordinates w) := by
  have he : fderiv ℝ (scalarEuclidean g) =
      fun y => (fderiv ℝ g (planeCoordinates y)).comp planeCoordinates.toContinuousLinearMap := by
    funext y
    simpa only [scalarEuclidean, ContinuousLinearEquiv.fderiv] using
      fderiv_comp y (hg.differentiable (by simp) _) planeCoordinates.differentiableAt
  rw [he]
  have hg' := ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
    (planeCoordinates x)).hasFDerivAt
  have hd := (hg'.comp x planeCoordinates.hasFDerivAt).clm_comp
    (hasFDerivAt_const (planeCoordinates.toContinuousLinearMap) x)
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  simp

theorem scalarLaplacian_eq_euclidean_trace {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Plane) :
    scalarLaplacian g x = ∑ j : Fin 2,
      fderiv ℝ (fderiv ℝ (scalarEuclidean g)) (planeCoordinates.symm x)
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [scalarEuclidean_second hg]
  have hbase : planeCoordinates (EuclideanSpace.single j 1) = PlanarHamiltonian.basis j := by
    ext k
    simp [planeCoordinates, PlanarHamiltonian.basis, Pi.single_apply]
  rw [planeCoordinates.apply_symm_apply, hbase]
  unfold spatialD
  rw [fderiv_clm_apply ((hg.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const _)]
  simp

theorem scalarLaplacian_bound_of_euclidean_hessian {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Plane) {B : ℝ}
    (hb : ‖fderiv ℝ (fderiv ℝ (scalarEuclidean g)) (planeCoordinates.symm x)‖ ≤ B) :
    |scalarLaplacian g x| ≤ 2 * B := by
  rw [scalarLaplacian_eq_euclidean_trace hg]
  exact hessian_trace_bound _ _ hb

end ForcedComputation.VelocityDetector

end

end OAI
