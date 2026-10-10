import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeDuality
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv

namespace OAI

/-! # The explicit adjoint free generator on Schwartz tests

The Fourier-test generator has coefficients -a+ib, -i|xi|² and the
negative half Euler derivative. These are computed from the exact
similarity action, with the twelve-dimensional Jacobian already included.
-/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasDerivAt_homogeneousPhysicalAmplitude (a b t : ℝ) :
    HasDerivAt (homogeneousPhysicalAmplitude a b)
      (homogeneousPhysicalAmplitude a b t * (-(a : ℂ) + Complex.I * (b : ℂ))) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ)
    (-(a : ℂ) + Complex.I * (b : ℂ)) t
  have hf : (fun s : ℝ => NormedSpace.exp (s • (-(a : ℂ) + Complex.I * (b : ℂ)))) =
      homogeneousPhysicalAmplitude a b := by
    funext s
    rw [Complex.real_smul, ← Complex.exp_eq_exp_ℂ, homogeneousPhysicalAmplitude_eq]
    congr 1
    ring
  have he := congrFun hf t
  rw [hf, he] at h
  exact h

end DefocusingNLS

end OAI
