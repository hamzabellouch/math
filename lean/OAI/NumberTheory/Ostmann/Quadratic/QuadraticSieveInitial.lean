import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveAdditiveStart
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSieveMonotone

namespace OAI

/-! # The initial exponent for the quadratic large sieve

The proved additive large sieve and quadratic reciprocity give the starting
exponent two in Heath-Brown's iteration, with an absolute constant.
-/

namespace Ostmann

 theorem quadraticSieveBound_initial (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    QuadraticSieveBound M N (4 * ((M : ℝ) + (N : ℝ) ^ 2)) := by
  have h := (quadraticSieveBound_additive N M hN).transpose
    (by positivity : 0 ≤ (M : ℝ) + 1 + (N : ℝ) ^ 2)
  apply h.mono_constant
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [sq_nonneg (N : ℝ)]

end Ostmann

end OAI
