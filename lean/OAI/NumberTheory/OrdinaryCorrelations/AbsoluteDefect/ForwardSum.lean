import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPhase

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

namespace OrdinaryInitialWidth
open OrdinaryCorrelations OrdinaryLocalAdditive Finset Filter MeasureTheory

def forwardSum (f : ℕ → ℂ) (α D y : ℝ) : ℂ :=
  ∑ n ∈ Ioc ⌊y⌋₊ ⌊y+D⌋₊, f n * phase (α*n)

end OrdinaryInitialWidth

end

end OAI
