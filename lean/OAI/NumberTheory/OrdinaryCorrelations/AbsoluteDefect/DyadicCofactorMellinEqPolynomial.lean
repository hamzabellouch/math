import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicCofactorMellin
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Coefficient

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace SourcePrimeFactor
open OrdinaryDirichletMeanSquare
lemma dyadicCofactorMellin_eq_polynomial (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (M : ℕ) (τ : ℝ) :
    dyadicCofactorMellin f χ P M τ=
      polynomial (Finset.Ioc M (2*M))
        (OrdinaryCofactorDyadicBound.coefficient P (characterModulation f χ))
        (fun n => Real.log n) τ := by
  unfold dyadicCofactorMellin polynomial
  apply Finset.sum_congr rfl
  intro n hn
  simp only [OrdinaryArchimedeanTwist.twist,
    OrdinaryCofactorDyadicBound.coefficient,primeCount,phase]
  rw [mul_comm τ (Real.log (n:ℝ))]
  ring

end SourcePrimeFactor

end

end OAI
