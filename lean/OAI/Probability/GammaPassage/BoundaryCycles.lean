import OAI.Probability.GammaPassage.BoundaryWinding
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace OAI

/-! Directed boundary cycles with nonzero signed ray-crossing count. -/
namespace PlanarFPP
open Finset Equiv

/-- A nonzero total weight on a fixed-point-free finite permutation has a
cycle of nonzero weight. -/
theorem exists_cycle_nonzero_sum {α : Type*} [Fintype α] [DecidableEq α]
    (p : Equiv.Perm α) (hp : ∀ x, p x ≠ x) (w : α → ℤ)
    (hw : ∑ x, w x ≠ 0) :
    ∃ x, ∑ y ∈ (p.toList x).toFinset, w y ≠ 0 := by
  classical
  let := Equiv.Perm.SameCycle.setoid p
  let Q := Quotient (Equiv.Perm.SameCycle.setoid p)
  let : Fintype Q := Fintype.ofFinite Q
  let c : α → Q := Quotient.mk (Equiv.Perm.SameCycle.setoid p)
  have hs := sum_fiberwise (univ : Finset α) c w
  by_contra hn
  push Not at hn
  have hz (q : Q) : ∑ y ∈ univ.filter (fun y => c y = q), w y = 0 := by
    induction q using Quotient.inductionOn with
    | h x =>
      change (∑ y ∈ univ.filter (fun y => c y = c x), w y) = 0
      have he : univ.filter (fun y => c y = c x) = (p.toList x).toFinset := by
        ext y
        simp only [mem_filter, mem_univ, true_and, List.mem_toFinset,
          Equiv.Perm.mem_toList_iff, Equiv.Perm.mem_support]
        constructor
        · intro hy
          exact ⟨(Quotient.exact hy : p.SameCycle y x).symm, hp x⟩
        · intro hy
          exact Quotient.sound hy.1.symm
      rw [he]
      exact hn x
  simp_rw [hz] at hs
  exact hw (by simpa using hs.symm)

/-- The source's enclosing boundary walk, with "nonzero winding" represented
by its exact signed intersections with the positive horizontal ray. -/
theorem exists_boundary_cycle (S : Finset Vertex) (h0 : (0 : Vertex) ∈ S) :
    ∃ x : BoundarySide S,
      let es := (boundaryPerm S).toList x
      es.Nodup ∧ 0 < es.length ∧
      (∀ e ∈ es, ((boundaryPerm S) e).val.tail = e.val.head) ∧
      (∀ e (he : e ∈ es), (es.next e he).val.tail = e.val.head) ∧
      (∑ e ∈ es.toFinset, e.val.rayCross) ≠ 0 := by
  classical
  have hw : ∑ e : BoundarySide S, e.val.rayCross ≠ 0 := by
    have hh := boundarySides_rayCross_sum S
    rw [ite_eq_left h0] at hh
    rw [Finset.sum_coe_sort]
    omega
  obtain ⟨x,hx⟩ := exists_cycle_nonzero_sum (boundaryPerm S)
    (boundaryPerm_ne_self S) (fun e => e.val.rayCross) hw
  refine ⟨x, Equiv.Perm.nodup_toList _ _, ?_, ?_, ?_, hx⟩
  · exact Equiv.Perm.length_toList_pos_of_mem_support _ _
      (Equiv.Perm.mem_support.mpr (boundaryPerm_ne_self S x))
  · intro e he
    exact boundaryPerm_tail S e
  · intro e he
    rw [Equiv.Perm.next_toList_eq_apply]
    exact boundaryPerm_tail S e

end PlanarFPP

end OAI
