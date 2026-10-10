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

namespace OrdinaryFrequencyChain
open Finset
attribute [local instance] Classical.propDecidable

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

end OrdinaryFrequencyChain

end

end OAI
