import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderWeightedIntegration
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderLiftH2

namespace OAI

/-! The gradient and Laplacian of a cutoff lifted from the horizontal plane. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

theorem verticallyPeriodic_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Space → E} (hp : VerticallyPeriodic g) (hg : Differentiable ℝ g) :
    VerticallyPeriodic (fderiv ℝ g) := by
  intro x n
  exact fderiv_translation hg (fun y => hp y n) x

theorem scalarPlaneLift_periodic (φ : Plane → ℝ) :
    VerticallyPeriodic (scalarPlaneLift φ) := by
  intro x n
  simp only [scalarPlaneLift, Function.comp_apply, map_add, map_smul,
    horizontalLinear_basis_two, smul_zero, add_zero]

theorem lifted_gradient_smooth {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (gradient (scalarPlaneLift φ)) := by
  have hs : ContDiff ℝ ∞ (scalarPlaneLift φ) := hφ.comp horizontalLinear.contDiff
  apply contDiff_pi.mpr
  intro j
  exact (hs.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem lifted_gradient_periodic {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    VerticallyPeriodic (gradient (scalarPlaneLift φ)) := by
  have hs : Differentiable ℝ (scalarPlaneLift φ) :=
    (hφ.comp horizontalLinear.contDiff).differentiable (by simp)
  intro x n
  ext j
  exact congrArg (fun A : Space →L[ℝ] ℝ => A (basis j))
    (verticallyPeriodic_fderiv (scalarPlaneLift_periodic φ) hs x n)

theorem lifted_gradient_support {φ : Plane → ℝ} (x : Space)
    (hx : horizontal x ∉ tsupport φ) : gradient (scalarPlaneLift φ) x = 0 := by
  ext j
  apply scalarSpatialD_horizontal_support (isClosed_tsupport φ)
    (fun y hy => by
      simp only [scalarPlaneLift, Function.comp_apply, horizontalLinear_eq]
      exact image_eq_zero_of_notMem_tsupport hy) j x hx

theorem lifted_gradient_divergence {φ : Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Space) :
    divergence (gradient (scalarPlaneLift φ)) x =
      VelocityDetector.scalarLaplacian φ (horizontalLinear x) := by
  have hg : Differentiable ℝ (gradient (scalarPlaneLift φ)) :=
    (lifted_gradient_smooth hφ).differentiable (by simp)
  have he (j : Fin 3) : derivative (gradient (scalarPlaneLift φ)) j x j =
      scalarSpatialD j (scalarSpatialD j (scalarPlaneLift φ)) x := by
    unfold derivative
    rw [← fderiv_coordinate hg]
    rfl
  have hh (j : Fin 2) :
      scalarSpatialD j.castSucc (scalarSpatialD j.castSucc (scalarPlaneLift φ)) x =
        PlanarHamiltonian.spatialD j (PlanarHamiltonian.spatialD j φ) (horizontalLinear x) := by
    rw [scalarPlaneLift_spatialD hφ,
      scalarPlaneLift_spatialD (PlanarHamiltonian.spatialD_smooth j hφ)]
    rfl
  have hv : scalarSpatialD 2 (scalarSpatialD 2 (scalarPlaneLift φ)) x = 0 := by
    rw [scalarPlaneLift_verticalD hφ]
    simp only [scalarSpatialD, fderiv_const_apply, zero_apply]
  simp only [divergence, he, Fin.sum_univ_three]
  change _ + _ + _ = _
  rw [show (0 : Fin 3) = (0 : Fin 2).castSucc from rfl, hh,
    show (1 : Fin 3) = (1 : Fin 2).castSucc from rfl, hh, hv]
  simp only [VelocityDetector.scalarLaplacian, Fin.sum_univ_two, add_zero]

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
