import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarMassCalculus

namespace OAI

/-! The periodic integration-by-parts identity used to transfer heat derivatives. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set MeasureTheory
open scoped ContDiff

theorem periodic_integral_mul_spatialD {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : PlanePeriodic f) (hpg : PlanePeriodic g) (j : Fin 2) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), f x * spatialD j g x) =
      -(∫ x in Icc (0 : Plane) (fun _ => 1), spatialD j f x * g x) := by
  have hp : PlanePeriodic (fun x => f x * g x) := by
    intro x n
    change f (x+fun j => (n j : ℝ)) * g (x+fun j => (n j : ℝ)) = f x * g x
    rw [hpf x n, hpg x n]
  have hz := integral_planar_periodic_derivative (hf.mul hg) hp j
  have he (x : Plane) : fderiv ℝ (fun y => f y * g y) x (PlanarHamiltonian.basis j) =
      spatialD j f x * g x + f x * spatialD j g x := by
    rw [fderiv_fun_mul (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, spatialD]
    ring
  simp_rw [he] at hz
  have hi₁ : IntegrableOn (fun x : Plane => spatialD j f x * g x)
      (Icc (0 : Plane) (fun _ => 1)) :=
    ((spatialD_smooth j hf).continuous.mul hg.continuous).integrableOn_Icc
  have hi₂ : IntegrableOn (fun x : Plane => f x * spatialD j g x)
      (Icc (0 : Plane) (fun _ => 1)) :=
    (hf.continuous.mul (spatialD_smooth j hg).continuous).integrableOn_Icc
  rw [integral_add hi₁ hi₂] at hz
  linarith

theorem periodic_integral_mul_spatialD_twice {f g : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : PlanePeriodic f) (hpg : PlanePeriodic g) (j : Fin 2) :
    (∫ x in Icc (0 : Plane) (fun _ => 1), f x * spatialD j (spatialD j g) x) =
      ∫ x in Icc (0 : Plane) (fun _ => 1), spatialD j (spatialD j f) x * g x := by
  rw [periodic_integral_mul_spatialD hf (spatialD_smooth j hg) hpf
    (spatialD_periodic hg hpg j) j,
    periodic_integral_mul_spatialD (spatialD_smooth j hf) hg
      (spatialD_periodic hf hpf j) hpg j, neg_neg]

end ForcedComputation.VelocityDetector

end

end OAI
