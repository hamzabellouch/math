import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportNorm
import Mathlib.LinearAlgebra.Trace

namespace OAI

/-!
# Balanced support data from trace-zero actions

For the Cartan model, the diagonal entries of the action in a homogeneous
word basis are sums of the letter weights. Unimodularity makes the trace
zero, yielding the balanced multiplicities of the support datum.
-/

namespace PolycyclicRecognition

open scoped BigOperators
open Module

variable {W I B J : Type*} [AddCommGroup W] [Module ℝ W]
  [Fintype I] [Fintype B] [Fintype J]

omit [Fintype B] in
/-- The total letter count in a word basis turns the diagonal trace identity
into the positive relation among the generator weights. -/
theorem balanced_letter_counts
    (α : I → Module.Dual ℝ W) (count : B → J → I → ℕ)
    (action : B → W → Matrix J J ℝ)
    (diagonal : ∀ b w j, action b w j j = ∑ i, (count b j i : ℝ) * α i w)
    (trace_zero : ∀ b w, Matrix.trace (action b w) = 0) (b : B) (w : W) :
    ∑ i, ((∑ j, count b j i : ℕ) : ℝ) * α i w = 0 := by
  simp only [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [← diagonal b w]
  exact trace_zero b w

/-- Build the segment-support norm data from homogeneous word counts and the
trace-zero matrix identity for the action on the nilpotent ideal. -/
def supportDatumOfTrace
    (α : I → Module.Dual ℝ W) (count : B → J → I → ℕ)
    (action : B → W → Matrix J J ℝ)
    (mandatory : ∀ b i, 0 < ∑ j, count b j i)
    (diagonal : ∀ b w j, action b w j j = ∑ i, (count b j i : ℝ) * α i w)
    (trace_zero : ∀ b w, Matrix.trace (action b w) = 0)
    (separates : ∀ w, (∀ i, α i w = 0) → w = 0) : SupportDatum W I B where
  weight := α
  multiplicity b i := ∑ j, count b j i
  positive := mandatory
  balanced := balanced_letter_counts α count action diagonal trace_zero
  separates := separates

/-- For a linear action, its trace-zero property can be checked in any basis. -/
theorem trace_zero_matrix_of_trace_zero
    {N : Type*} [AddCommGroup N] [Module ℝ N] [DecidableEq J]
    (basis : Basis J ℝ N) (A : W →ₗ[ℝ] Module.End ℝ N)
    (h : ∀ w, LinearMap.trace ℝ N (A w) = 0) (w : W) :
    Matrix.trace (LinearMap.toMatrix basis basis (A w)) = 0 := by
  rw [← LinearMap.trace_eq_matrix_trace ℝ basis]
  exact h w

end PolycyclicRecognition

end OAI
