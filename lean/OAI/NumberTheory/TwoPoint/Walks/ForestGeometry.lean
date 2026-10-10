import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-!
# The independent-direction obstruction to an incidence cycle

A hypothetical simple cycle of line and point vertices uses each line
once. Its successive point differences lie along distinct independent
directions. Telescoping around the cycle forces every difference to
vanish, contradicting distinct adjacent points. This is the algebraic
acyclicity step in `q:forest-code`.
-/

namespace TwoPointCorrelations

open Finset

theorem independent_directions_closed_chain {K ι V : Type*} [Field K]
    [Fintype ι] [AddCommGroup V] [Module K V]
    (d : ι → V) (hd : LinearIndependent K d) (p : ι → V)
    (next : Equiv.Perm ι) (c : ι → K)
    (hstep : ∀ i, p (next i) - p i = c i • d i) : ∀ i, c i = 0 := by
  apply Fintype.linearIndependent_iff.mp hd c
  simp_rw [← hstep]
  rw [sum_sub_distrib, Equiv.sum_comp next p, sub_self]

/-- Distinct independent line directions cannot support a nontrivial
closed polygon, regardless of where the affine lines are based. -/
theorem independent_lines_cycle_degenerate {K ι V : Type*} [Field K]
    [Fintype ι] [AddCommGroup V] [Module K V]
    (d : ι → V) (hd : LinearIndependent K d) (anchor p : ι → V)
    (next : Equiv.Perm ι)
    (hincidence : ∀ i, ∃ s t : K,
      p i = anchor i + s • d i ∧ p (next i) = anchor i + t • d i) :
    ∀ i, p (next i) = p i := by
  choose s t hs ht using hincidence
  have hstep (i : ι) : p (next i) - p i = (t i - s i) • d i := by
    rw [ht i, hs i, sub_smul]
    abel
  have hc := independent_directions_closed_chain d hd p next (fun i => t i - s i) hstep
  intro i
  apply sub_eq_zero.mp
  rw [hstep i, hc i, zero_smul]

end TwoPointCorrelations

end OAI
