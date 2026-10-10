import OAI.NumberTheory.JointDickman.Amplification.ArithmeticInputs
import Mathlib.NumberTheory.DirichletCharacter.Bounds

namespace OAI

/-!
# The published character estimate

The input is the Siegel–Walfisz specialization of Singha Roy,
*The Landau–Selberg–Delange method for products of Dirichlet L-functions,
and applications, I*, arXiv:2511.15928v1, Theorem 1.1 and Corollary 1.2,
with Siegel's bound (Koukoulopoulos, Theorem 12.10). Take ν = 1, the
exponent z at one nonprincipal character, and zero at every other
character. The Euler correction is absolutely convergent for Re(s)>1/2;
the principal exponent is zero, so all the main coefficients vanish.
This is an explicit conditional input, not a proof of that analytic result.
-/

namespace JointDickman

open Finset

/-- Twist the squarefree coefficients, before removing any small primes. -/
noncomputable def squarefreeCharacterSum {q : ℕ}
    (χ : DirichletCharacter ℂ q) (z Y : ℝ) : ℂ :=
  ∑ n ∈ Ioc 0 ⌊Y⌋₊, (squarefreeWeight z n : ℂ) * χ (n : ZMod q)

namespace PublishedInputs

/-- Only the two exponents and the arbitrary fixed logarithmic saving
needed for the moving-cutoff argument are retained. -/
def SquarefreeCharacterEstimateInput : Prop :=
  ∀ z : ℝ, z = 1 / 4 ∨ z = 1 / 2 →
    ∀ C D : ℝ, 0 < C → 0 ≤ D → ∃ K : ℝ, 0 ≤ K ∧
      ∀ Y : ℝ, 3 ≤ Y → ∀ q : ℕ, ∀ [NeZero q],
        (q : ℝ) ≤ (Real.log Y) ^ C →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖squarefreeCharacterSum χ z Y‖ ≤ K * Y * (Real.log Y) ^ (-D)

end PublishedInputs

end JointDickman

end OAI
