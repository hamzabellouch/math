import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model

namespace OAI

noncomputable section
namespace VelocityDetection.BurstCalculus
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
variable {n : ℕ}

theorem spatialD_time_mul (i : Fin n) (b : ℝ → ℝ) (f : ScalarField n) :
    spatialD i (fun t X => b t*f t X) = fun t X => b t*spatialD i f t X := by
  funext t X
  exact deriv_const_mul_field (b t)

theorem advection_time_mul (a : VectorField n) (b : ℝ → ℝ) (f : ScalarField n) :
    advection a (fun t X => b t*f t X) = fun t X => b t*advection a f t X := by
  funext t X
  simp only [advection,spatialD_time_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem laplacian_time_mul (b : ℝ → ℝ) (f : ScalarField n) :
    laplacian (fun t X => b t*f t X) = fun t X => b t*laplacian f t X := by
  funext t X
  simp only [laplacian,spatialD_time_mul,Finset.mul_sum]

theorem divergence_time_smul (b τ : ℝ → ℝ) (a : VectorField n) (t : ℝ) (X : Coord n) :
    divergence (fun s Y => b s • a (τ s) Y) t X = b t*divergence a (τ t) X := by
  simp only [divergence,Pi.smul_apply,smul_eq_mul,spatialD_time_mul,Finset.mul_sum]
  rfl

end VelocityDetection.BurstCalculus
end

end OAI
