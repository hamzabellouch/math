import OAI.Combinatorics.HoneycombChords.Bridges
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace OAI

/-! Rational spectral interpolation conditions for the critical bridge mass.

The denominator and confluent node multiplicities follow the finite strip
transfer calculation in the companion paper on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.FiniteFunctional
noncomputable def angle : ℝ := Real.pi / 8

noncomputable def interpolationDenominator (N : ℕ) (X : ℂ) : ℂ :=
  (X+1)^N*(X+(Real.cos (2*angle):ℂ))^(N+1)

noncomputable def interpolant (N : ℕ) (ρ : ℂ) (P : Polynomial ℂ) (u : ℝ) : ℂ :=
  let X : ℂ := (Real.cos (2*u):ℂ)
  4*X+ρ+P.eval X/interpolationDenominator N X

def PhysicalSpectralInterpolation : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∃ (B : ℝ) (ρ : ℂ) (P : Polynomial ℂ),
    0 ≤ B ∧ bridgeMass N = ENNReal.ofReal B ∧ P.natDegree < 2*N+1 ∧
    interpolant N ρ P 0 = 2*(B:ℂ) ∧
    interpolant N ρ P (3*angle/2) = 0 ∧
    interpolant N ρ P (5*angle/2) = 0 ∧
    (∀ j : ℕ, j < 2*N →
      iteratedDeriv j (fun u : ℝ => interpolant N ρ P (u-angle)+
        interpolant N ρ P (u+angle)-interpolant N ρ P u) 0 = 0) ∧
    (∀ j : ℕ, j < N →
      iteratedDeriv j (fun u : ℝ => interpolant N ρ P (u-angle)+
        interpolant N ρ P (u+angle)-interpolant N ρ P u) angle = 0)

end CriticalHoneycomb.FiniteFunctional

end

end OAI
