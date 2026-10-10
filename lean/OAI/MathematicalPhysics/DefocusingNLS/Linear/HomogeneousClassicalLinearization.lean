import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousClassicalGenerator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousGeneratorCoordinates

namespace OAI

/-! # Classical equations for actual linearized generator vectors

The potential here is the proved derivative of the odd-power nonlinearity
on the faithful Y space. Neither a spatial smoothness assumption nor an
independent differential-operator eigenvalue hypothesis is introduced.
-/

open Set
open scoped Laplacian ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLinearized_domain_classical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q u v : HomogeneousY a k)
    (hu : HasDerivWithinAt (fun t : ℝ => homogeneousFreeOperator a b k t ha ha1 hk u)
      (v - homogeneousLinearizedPotential a k ha ha1 hk m q u) (Ici 0) 0) (x : E) :
    homogeneousPhysicalCLM a k ha ha1 hk v x =
      Complex.I * Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x -
        (1 / 2 : ℂ) * fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x x +
        (-(a : ℂ) + Complex.I * (b : ℂ)) * homogeneousPhysicalCLM a k ha ha1 hk u x -
        Complex.I * oddPowerDerivative m (homogeneousPhysicalCLM a k ha ha1 hk q x)
          (homogeneousPhysicalCLM a k ha ha1 hk u x) := by
  have h := homogeneousFree_generator_classical a b k ha ha1 hk u
    (v - homogeneousLinearizedPotential a k ha ha1 hk m q u) hu x
  rw [map_sub, ZeroAtInftyContinuousMap.sub_apply, homogeneousLinearizedPotential_physical] at h
  linear_combination h

theorem homogeneousLinearized_generator_classical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (q u v : HomogeneousY a k)
    (hu : HasDerivWithinAt (fun t : ℝ =>
      homogeneousLinearizedStep a b k ha ha1 hk m q t.toNNReal u) v (Ici 0) 0) (x : E) :
    homogeneousPhysicalCLM a k ha ha1 hk v x =
      Complex.I * Δ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x -
        (1 / 2 : ℂ) * fderiv ℝ (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) x x +
        (-(a : ℂ) + Complex.I * (b : ℂ)) * homogeneousPhysicalCLM a k ha ha1 hk u x -
        Complex.I * oddPowerDerivative m (homogeneousPhysicalCLM a k ha ha1 hk q x)
          (homogeneousPhysicalCLM a k ha ha1 hk u x) :=
  homogeneousLinearized_domain_classical a b k ha ha1 hk m q u v
    (homogeneousFree_derivWithin_of_linearized a b k ha ha1 hk m q u v hu) x

end DefocusingNLS

end OAI
