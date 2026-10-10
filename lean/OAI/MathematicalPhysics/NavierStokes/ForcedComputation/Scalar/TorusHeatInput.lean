import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusScalarInput
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace OAI

/-! The isotropic two-dimensional periodic heat kernel and its Gaussian bound.

P. Maheux, Notes on Heat Kernels on Infinite dimensional Torus (16 February
2008), Sections 2.1 and 3.1, and Theorem 3.1, equation (3.15), pp. 5, 10--11.
The isotropic two-dimensional kernel is rescaled from period 2π to period
one. Its generator is the coordinate Laplacian, and its Gaussian estimate
is the first upper bound in (3.15). Source: https://idpoisson.fr/maheux/InfiniteTorusV2.pdf
-/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory
open scoped ContDiff BigOperators

/-- Squared Euclidean distance to the nearest lattice point, using the
centered representative in each coordinate. -/
def torusDistanceSq (x : Plane) : ℝ :=
  ∑ j : Fin 2, (x j - (⌊x j + 1 / 2⌋ : ℤ)) ^ 2

def torusHeatKernel (t : ℝ) (x : Plane) : ℝ :=
  (4 * Real.pi * t)⁻¹ * ∑' k : Fin 2 → ℤ,
    Real.exp (-(∑ j : Fin 2, (x j + (k j : ℝ)) ^ 2) / (4 * t))

def torusHeatEvolution (g : Plane → ℝ) (t : ℝ) (x : Plane) : ℝ :=
  if t ≤ 0 then g x else
    ∫ y in Icc (0 : Plane) (fun _ => 1), torusHeatKernel t (x - y) * g y

/-- The flat-torus specialization of the heat representation and Gaussian bound. -/
structure TorusHeatInput : Prop where
  continuous : ∀ t, 0 < t → Continuous (torusHeatKernel t)
  solution : ∀ (T : ℝ), 0 ≤ T → ∀ (g : Plane → ℝ),
    ContDiff ℝ ∞ g → PlanePeriodic g →
    TorusScalarSolution T 1 (fun _ _ => 0) (fun _ _ => 0) (torusHeatEvolution g) g
  gaussian : ∀ t, 0 < t → ∀ x,
    torusHeatKernel t x ≤
      4 * (1 + Real.sqrt (1 / (4 * Real.pi * t))) ^ 2 *
        Real.exp (-(torusDistanceSq x) / (4 * t))

theorem torusDistanceSq_nonneg (x : Plane) : 0 ≤ torusDistanceSq x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem torusHeatKernel_nonneg {t : ℝ} (ht : 0 < t) (x : Plane) :
    0 ≤ torusHeatKernel t x := by
  unfold torusHeatKernel
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (tsum_nonneg (fun _ => (Real.exp_pos _).le))

end ForcedComputation.VelocityDetector

end

end OAI
