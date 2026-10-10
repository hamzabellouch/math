import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Linearity

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W05

theorem twisted_mangoldt_eq_logDerivative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv χ.LFunction s / χ.LFunction s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs

theorem combined_mangoldt_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) +
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  change LSeriesSummable
    ((fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) +
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))) s
  apply LSeriesSummable.add
  · exact ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  · exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs

theorem combined_mangoldt_eq_logDerivatives {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) +
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv riemannZeta s / riemannZeta s +
      -deriv χ.LFunction s / χ.LFunction s := by
  calc
    _ = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) s +
        LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
      exact LSeries_add
        (f := fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
        (g := fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ))
        (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
        (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs)
    _ = _ := congrArg₂ (fun x y : ℂ => x + y)
      (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs)
      (twisted_mangoldt_eq_logDerivative χ hs)

end WeightedTorusJets.W05

end

end SiegelZeros

end OAI
