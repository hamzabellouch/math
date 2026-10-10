import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarDerivativeBounds

namespace OAI

/-! Spatial calculus for the triangular velocity U(Y,z) = (a(Y), w(Y)).
This is the scalar-to-Navier–Stokes reduction used by both detectors. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff BigOperators

def triangularLift (a : Plane → Plane) (w : Plane → ℝ) (x : Space) : Space :=
  letI := ShearFlows.neZeroThree
  planeInclusion (a (horizontalLinear x)) + w (horizontalLinear x) • basis 2

theorem horizontalLinear_eq (x : Space) : horizontalLinear x = horizontal x := by
  ext j
  fin_cases j <;> rfl

theorem triangularLift_eq (a : Plane → Plane) (w : Plane → ℝ) (x : Space) :
    triangularLift a w x = atHeight (a (horizontal x)) (w (horizontal x)) := by
  unfold triangularLift
  rw [horizontalLinear_eq]
  ext j
  fin_cases j <;> simp [planeInclusion, atHeight, basis]

theorem triangularLift_smooth {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (triangularLift a w) :=
  (planeInclusion.contDiff.comp (ha.comp horizontalLinear.contDiff)).add
    ((hw.comp horizontalLinear.contDiff).smul contDiff_const)

theorem triangularLift_fderiv {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) (x v : Space) :
    fderiv ℝ (triangularLift a w) x v =
      planeInclusion (fderiv ℝ a (horizontalLinear x) (horizontalLinear v)) +
        fderiv ℝ w (horizontalLinear x) (horizontalLinear v) • basis 2 := by
  have hA := planeInclusion.hasFDerivAt.comp x
    (((ha.differentiable (by simp) (horizontalLinear x)).hasFDerivAt).comp x
      horizontalLinear.hasFDerivAt)
  have hW := (((hw.differentiable (by simp) (horizontalLinear x)).hasFDerivAt).comp x
      horizontalLinear.hasFDerivAt).smul_const (basis 2)
  have hd := hA.add hW
  change HasFDerivAt (triangularLift a w) _ x at hd
  rw [hd.fderiv]
  rfl

theorem horizontalLinear_basis (j : Fin 2) :
    horizontalLinear (basis j.castSucc) = PlanarHamiltonian.basis j := by
  ext k
  fin_cases j <;> fin_cases k <;>
    simp [horizontalLinear, basis, PlanarHamiltonian.basis]

theorem horizontalLinear_basis_two : horizontalLinear (basis 2) = 0 := by
  ext k
  fin_cases k <;> simp [horizontalLinear, basis]

theorem triangularLift_derivative {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) (j : Fin 2) :
    derivative (triangularLift a w) j.castSucc =
      triangularLift (fun y => fderiv ℝ a y (PlanarHamiltonian.basis j))
        (PlanarHamiltonian.spatialD j w) := by
  funext x
  rw [derivative, triangularLift_fderiv ha hw, horizontalLinear_basis]
  rfl

theorem triangularLift_vertical_derivative {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) :
    derivative (triangularLift a w) 2 = fun _ => 0 := by
  funext x
  rw [derivative, triangularLift_fderiv ha hw, horizontalLinear_basis_two]
  simp

theorem triangularLift_divergence {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) (x : Space) :
    divergence (triangularLift a w) x = PlanarHamiltonian.divergence a (horizontal x) := by
  have h₀ := triangularLift_derivative ha hw (0 : Fin 2)
  have h₁ := triangularLift_derivative ha hw (1 : Fin 2)
  change derivative (triangularLift a w) 0 = _ at h₀
  change derivative (triangularLift a w) 1 = _ at h₁
  rw [divergence, Fin.sum_univ_three, h₀, h₁, triangularLift_vertical_derivative ha hw]
  simp only [triangularLift_eq, atHeight, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply, add_zero]
  unfold PlanarHamiltonian.divergence PlanarHamiltonian.spatialD
  rw [Fin.sum_univ_two]
  congr 1 <;> rw [fderiv_apply (ha.differentiable (by simp) (horizontal x))]
  <;> rfl

theorem horizontal_triangularLift (a : Plane → Plane) (w : Plane → ℝ) (x : Space) :
    horizontalLinear (triangularLift a w x) = a (horizontalLinear x) := by
  ext j
  fin_cases j <;> simp [triangularLift, horizontalLinear, planeInclusion, basis]

theorem triangularLift_advection {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) (x : Space) :
    advection (triangularLift a w) x =
      triangularLift (fun y => fderiv ℝ a y (a y))
        (fun y => fderiv ℝ w y (a y)) x := by
  rw [advection, triangularLift_fderiv ha hw, horizontal_triangularLift]
  rfl

def planarVectorLaplacian (a : Plane → Plane) (y : Plane) : Plane :=
  ∑ j : Fin 2, fderiv ℝ (fun z => fderiv ℝ a z (PlanarHamiltonian.basis j)) y
    (PlanarHamiltonian.basis j)

theorem triangularLift_laplacian {a : Plane → Plane} {w : Plane → ℝ}
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w) (x : Space) :
    laplacian (triangularLift a w) x =
      triangularLift (planarVectorLaplacian a) (scalarLaplacian w) x := by
  have hd (j : Fin 2) :
      fderiv ℝ (derivative (triangularLift a w) j.castSucc) x (basis j.castSucc) =
        planeInclusion
          (fderiv ℝ (fun z => fderiv ℝ a z (PlanarHamiltonian.basis j)) (horizontalLinear x)
            (PlanarHamiltonian.basis j)) +
          PlanarHamiltonian.spatialD j (PlanarHamiltonian.spatialD j w) (horizontalLinear x) • basis 2 := by
    rw [triangularLift_derivative ha hw,
      triangularLift_fderiv
        ((ha.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
        (PlanarHamiltonian.spatialD_smooth j hw), horizontalLinear_basis]
    rfl
  have hz : fderiv ℝ (derivative (triangularLift a w) 2) x (basis 2) = 0 := by
    rw [triangularLift_vertical_derivative ha hw]
    simp
  change (∑ j : Fin 3, fderiv ℝ (derivative (triangularLift a w) j) x (basis j)) = _
  have hd₀ := hd (0 : Fin 2)
  have hd₁ := hd (1 : Fin 2)
  change fderiv ℝ (derivative (triangularLift a w) 0) x (basis 0) = _ at hd₀
  change fderiv ℝ (derivative (triangularLift a w) 1) x (basis 1) = _ at hd₁
  rw [Fin.sum_univ_three, hd₀, hd₁, hz]
  simp only [triangularLift, planarVectorLaplacian, scalarLaplacian,
    Fin.sum_univ_two, map_add, add_smul]
  abel

end ForcedComputation.VelocityDetector

end

end OAI
