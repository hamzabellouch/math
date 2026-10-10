import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ForwardSum

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryTwistWidth
open OrdinaryCorrelations OrdinaryInitialWidth OrdinaryLocalAdditive Finset Filter MeasureTheory

def primeCount (P : Finset ℕ) (n : ℕ) : ℕ := (P.filter (fun p=>p∣n)).card

noncomputable def twist (f : ℕ→ℂ) (P : Finset ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  f n*phase (t*primeCount P n)

end OrdinaryTwistWidth

end

end OAI
