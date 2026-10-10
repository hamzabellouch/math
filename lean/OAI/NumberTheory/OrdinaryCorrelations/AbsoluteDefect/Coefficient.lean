import Mathlib

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

namespace OrdinaryCofactorDyadicBound

def coefficient (P : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (f n/(((P.filter (fun p => p∣n)).card:ℂ)+1))/(n:ℂ)

end OrdinaryCofactorDyadicBound

end

end OAI
