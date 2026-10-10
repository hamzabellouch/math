import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneBarrier

namespace OAI

/-! Translation and dilation of scalar test functions on the plane. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian
open scoped ContDiff

def scalarAffineScale (r : ℝ) (c x : Plane) : Plane := r • (x - c)

theorem scalarAffineScale_smooth (r : ℝ) (c : Plane) :
    ContDiff ℝ ∞ (scalarAffineScale r c) := by
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ∞ (fun x : Plane => r * (x j - c j))
  exact contDiff_const.mul ((contDiff_apply ℝ ℝ j).sub contDiff_const)

theorem scalarAffineScale_hasFDerivAt (r : ℝ) (c x : Plane) :
    HasFDerivAt (scalarAffineScale r c) (r • ContinuousLinearMap.id ℝ Plane) x :=
  ((hasFDerivAt_id x).sub_const c).const_smul r

theorem spatialD_affine_scale {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (c : Plane) (j : Fin 2) :
    spatialD j (fun x => f (scalarAffineScale r c x)) =
      fun x => r * spatialD j f (scalarAffineScale r c x) := by
  funext x
  have hd := ((hf.differentiable (by simp) (scalarAffineScale r c x)).hasFDerivAt).comp x
    (scalarAffineScale_hasFDerivAt r c x)
  change fderiv ℝ (fun x => f (scalarAffineScale r c x)) x (basis j) = _
  change HasFDerivAt (fun x => f (scalarAffineScale r c x)) _ x at hd
  rw [hd.fderiv]
  simp [spatialD, smul_eq_mul]

theorem scalarLaplacian_affine_scale {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (c x : Plane) :
    scalarLaplacian (fun y => f (scalarAffineScale r c y)) x =
      r ^ 2 * scalarLaplacian f (scalarAffineScale r c x) := by
  have he (j : Fin 2) :
      spatialD j (spatialD j (fun y => f (scalarAffineScale r c y))) x =
        r ^ 2 * spatialD j (spatialD j f) (scalarAffineScale r c x) := by
    rw [spatialD_affine_scale hf]
    have hs : ContDiff ℝ ∞ (fun y => spatialD j f (scalarAffineScale r c y)) :=
      (spatialD_smooth j hf).comp (scalarAffineScale_smooth r c)
    rw [spatialD_const_mul hs]
    rw [spatialD_affine_scale (spatialD_smooth j hf)]
    ring
  simp only [scalarLaplacian, he, Finset.mul_sum]

end ForcedComputation.VelocityDetector

end

end OAI
