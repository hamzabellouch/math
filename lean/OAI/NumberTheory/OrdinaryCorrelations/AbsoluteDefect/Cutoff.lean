import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OrdinaryTwistWidthBasic

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
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryAnalyticCutoff
open OrdinaryCorrelations SourceRoughFourier OrdinaryTwistWidth Finset Filter
noncomputable def cutoff (phi : ℝ→ℝ) (P : Finset ℕ) (mu : ℝ) (n : ℕ) : ℂ :=
  (phi (((primeCount P n:ℝ)-mu)/Real.sqrt mu):ℂ)
end OrdinaryAnalyticCutoff

end

end OAI
