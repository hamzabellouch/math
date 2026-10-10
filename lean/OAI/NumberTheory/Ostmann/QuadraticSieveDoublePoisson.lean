import OAI.NumberTheory.Ostmann.QuadraticSieveCoprimeQuadraticPoisson
import OAI.NumberTheory.Ostmann.QuadraticSieveDualReindex

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform ArithmeticFunction.Moebius

theorem coprime_quadratic_poisson_dual {q : ℕ} [NeZero q]
    (hq : Odd q) (hsq : Squarefree q) (hq1 : 1 < q)
    (k : ℕ) (hk : k ≠ 0) (M : ℝ) (hM : 0 < M) (W : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, if Nat.Coprime m.natAbs k then
      (jacobiSym m q : ℂ) * W ((m : ℝ) / M) else 0) =
      ∑ e ∈ k.divisors, ∑ a ∈ signedSquarefreeMultipliers,
        (μ e : ℂ) * ((M / (e * q) : ℝ) : ℂ) *
          gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
          ∑' b : OddSquarefreeIndex, (jacobiSym ((e : ℤ) * a * (b.val : ℤ)) q : ℂ) *
            dualSquareSum W (a : ℝ) (e : ℝ) M (b.val : ℝ) q := by
  rw [coprime_quadratic_poisson hq hsq k hk M hM W]
  apply Finset.sum_congr rfl
  intro e he
  have hep : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_mem_divisors he
  have harg (h : ℤ) : (h : ℝ) * (M / e) / q = (h : ℝ) * M / (e * q) := by ring
  simp_rw [harg]
  rw [dual_jacobi_series_eq_signed_dualSquareSum W (e : ℝ) M q hep hM hq1]
  have hscale : ((M / e) / q : ℝ) = M / (e * q) := by ring
  rw [hscale, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro b
  simp only [jacobiSym.mul_left, Int.cast_mul]
  ring

end Ostmann.QuadraticSieve

end OAI
