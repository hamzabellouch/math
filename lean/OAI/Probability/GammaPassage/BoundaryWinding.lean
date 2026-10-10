import OAI.Probability.GammaPassage.BoundaryGeometry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI

namespace PlanarFPP
open Finset

def SquareSide.rayCross (e : SquareSide) : ℤ :=
  match e.2 with
  | .north => if e.1.2 = 0 ∧ 0 ≤ e.1.1 then 1 else 0
  | .south => if e.1.2 = 0 ∧ 0 < e.1.1 then -1 else 0
  | _ => 0

def SquareSide.opposite (e : SquareSide) : SquareSide :=
  (e.1 + e.2.outward, e.2.reverse)

@[simp] theorem SquareSide.opposite_opposite (e : SquareSide) :
    e.opposite.opposite = e := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp [opposite, Step.outward, Step.right, Step.reverse, Step.delta]

theorem SquareSide.opposite_ne_self (e : SquareSide) : e.opposite ≠ e := by
  intro h
  have hh := congrArg Prod.snd h
  cases hd : e.2 <;> simp [opposite, hd, Step.reverse] at hh

@[simp] theorem SquareSide.rayCross_opposite (e : SquareSide) :
    e.opposite.rayCross = -e.rayCross := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp [opposite, rayCross, Step.outward, Step.right,
    Step.reverse, Step.delta] <;> split_ifs <;> omega

theorem square_rayCross_sum (q : Vertex) :
    ∑ d : Step, SquareSide.rayCross (q,d) = if q = 0 then 1 else 0 := by
  have hu : (univ : Finset Step) = {Step.east,Step.west,Step.north,Step.south} := rfl
  rw [hu]
  rcases q with ⟨x,y⟩
  simp [SquareSide.rayCross, Prod.ext_iff]
  split_ifs <;> omega

def internalSides (S : Finset Vertex) : Finset SquareSide :=
  (S ×ˢ univ).filter (fun e => e.1 + e.2.outward ∈ S)

theorem internalSides_opposite (S : Finset Vertex) (e : SquareSide)
    (he : e ∈ internalSides S) : e.opposite ∈ internalSides S := by
  simp only [internalSides, mem_filter, mem_product, mem_univ, and_true] at he ⊢
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [SquareSide.opposite, Step.outward,
    Step.right, Step.reverse, Step.delta, Prod.mk_add_mk, add_assoc]

theorem internalSides_rayCross_sum (S : Finset Vertex) :
    ∑ e ∈ internalSides S, e.rayCross = 0 := by
  refine sum_involution (fun e _ => e.opposite) ?_ ?_ (internalSides_opposite S) ?_
  · intro e he
    simp
  · intro e he hh
    exact e.opposite_ne_self
  · intro e he
    exact e.opposite_opposite

/-- Before cancellation, only the square centered at zero crosses the ray
with net signed count one. Shared sides have opposite counts and cancel. -/
theorem boundarySides_rayCross_sum (S : Finset Vertex) :
    ∑ e ∈ boundarySides S, e.rayCross = if (0 : Vertex) ∈ S then 1 else 0 := by
  classical
  have hsplit := sum_filter_add_sum_filter_not (S ×ˢ (univ : Finset Step))
    (fun e : SquareSide => e.1 + e.2.outward ∈ S) SquareSide.rayCross
  change (∑ e ∈ internalSides S, e.rayCross) +
    (∑ e ∈ boundarySides S, e.rayCross) = _ at hsplit
  rw [internalSides_rayCross_sum, zero_add] at hsplit
  rw [hsplit, sum_product]
  change (∑ q ∈ S, ∑ d : Step, SquareSide.rayCross (q,d)) = _
  simp_rw [square_rayCross_sum]
  by_cases h0 : (0 : Vertex) ∈ S
  · rw [ite_eq_left h0]
    calc
      _ = (if (0 : Vertex) = 0 then (1 : ℤ) else 0) := by
        apply sum_eq_single 0
        · intro b hb hne
          exact ite_eq_right hne
        · exact fun hh => False.elim (hh h0)
      _ = 1 := ite_eq_left rfl
  · rw [ite_eq_right h0]
    apply sum_eq_zero
    intro q hq
    apply ite_eq_right
    intro hh
    exact h0 (hh ▸ hq)

end PlanarFPP

end OAI
