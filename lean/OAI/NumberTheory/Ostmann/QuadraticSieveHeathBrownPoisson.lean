import OAI.NumberTheory.Ostmann.QuadraticSieveGauss
import OAI.NumberTheory.Ostmann.QuadraticSievePoissonDilation

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap FourierTransform

theorem jacobi_divModEquiv (q : ℕ) [NeZero q] (m : ℤ) :
    (jacobiSym ((Int.divModEquiv q m).2.val : ℤ) q : ℂ) = (jacobiSym m q : ℂ) := by
  have hr : (Int.divModEquiv q m).1 * (q : ℤ) +
      ((Int.divModEquiv q m).2.val : ℤ) = m := (Int.divModEquiv q).symm_apply_apply m
  have hmod : (((Int.divModEquiv q m).2.val : ℕ) : ZMod q) = (m : ZMod q) := by
    have hz := congrArg (fun z : ℤ => (z : ZMod q)) hr
    simpa using hz
  rw [← jacobiDirichletCharacter_natCast, ← jacobiDirichletCharacter_intCast, hmod]

theorem quadratic_poisson {q : ℕ} [NeZero q] (hq : Odd q) (hsq : Squarefree q)
    (M : ℝ) (hM : 0 < M) (f : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, (jacobiSym m q : ℂ) * f ((m : ℝ) / M)) =
      ((M / q : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
        ∑' h : ℤ, (jacobiSym h q : ℂ) * 𝓕 f ((h : ℝ) * M / q) := by
  have hp := periodic_weighted_poisson_scaled q M hM
    (fun a : Fin q => (jacobiSym (a.val : ℤ) q : ℂ)) f
  simp_rw [jacobi_divModEquiv, finite_jacobi_gauss_transform hq hsq] at hp
  calc
    _ = ∑' h : ℤ, ((M / q : ℝ) : ℂ) *
        ((jacobiSym h q : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
        𝓕 f ((h : ℝ) * M / q) := hp
    _ = ∑' h : ℤ,
        (((M / q : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar) *
        ((jacobiSym h q : ℂ) * 𝓕 f ((h : ℝ) * M / q)) := by
      apply tsum_congr
      intro h
      ring
    _ = _ := tsum_mul_left

end Ostmann.QuadraticSieve

end OAI
