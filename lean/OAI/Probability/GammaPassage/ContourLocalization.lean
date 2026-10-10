import OAI.Probability.GammaPassage.SquareLoops
import OAI.Probability.GammaPassage.OrientedSelection

namespace OAI

/-! A loop with nonzero ray-crossing count starts within O(m) of zero.
This supplies the location factor in the source's contour enumeration. -/
namespace PlanarFPP
open Finset

namespace SquareSide

def axisCross (e : SquareSide) : ℤ :=
  match e.2 with
  | .north => if e.1.2 = 0 then 1 else 0
  | .south => if e.1.2 = 0 then -1 else 0
  | _ => 0

def aboveAxis (p : Vertex) : ℤ := if 0 < p.2 then 1 else 0

theorem axisCross_eq (e : SquareSide) :
    e.axisCross = aboveAxis e.head - aboveAxis e.tail := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp [axisCross, aboveAxis, head, tail, Step.corner, Step.delta] <;>
    split_ifs <;> omega

theorem rayCross_eq_axisCross (e : SquareSide) (hx : 0 < e.tail.1) :
    e.rayCross = e.axisCross := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [rayCross, axisCross, tail, Step.corner]
  split_ifs <;> omega

theorem rayCross_ne_zero_location (e : SquareSide) (he : e.rayCross ≠ 0) :
    0 < e.tail.1 ∧ 0 ≤ e.tail.2 ∧ e.tail.2 ≤ 1 := by
  rcases e with ⟨⟨x,y⟩,d⟩
  cases d <;> simp_all [rayCross, tail, Step.corner]
  omega

end SquareSide

namespace SquareLoop
variable {m : ℕ}

theorem sum_axisCross (c : SquareLoop m) : ∑ i, (c.side i).axisCross = 0 := by
  simp_rw [SquareSide.axisCross_eq, ← c.follows]
  rw [sum_sub_distrib, Equiv.sum_comp (finRotate m)
    (fun i => SquareSide.aboveAxis (c.side i).tail), sub_self]

theorem winding_locations (c : SquareLoop m) (hc : c.winding ≠ 0) :
    (∃ i, (c.side i).tail.1 ≤ 0) ∧
    (∃ i, 0 < (c.side i).tail.1 ∧ 0 ≤ (c.side i).tail.2 ∧ (c.side i).tail.2 ≤ 1) := by
  constructor
  · by_contra hn
    push Not at hn
    apply hc
    change (∑ i, (c.side i).rayCross) = 0
    simp_rw [SquareSide.rayCross_eq_axisCross _ (hn _)]
    exact c.sum_axisCross
  · have he : ∃ i, (c.side i).rayCross ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hc (sum_eq_zero (fun i _ => hn i))
    obtain ⟨i,hi⟩ := he
    exact ⟨i,SquareSide.rayCross_ne_zero_location _ hi⟩

theorem tail_bounds (c : SquareLoop m) (hm : 0 < m) (i : Fin m) :
    (c.side ⟨0,hm⟩).tail.1 - i.val ≤ (c.side i).tail.1 ∧
    (c.side i).tail.1 ≤ (c.side ⟨0,hm⟩).tail.1 + i.val ∧
    (c.side ⟨0,hm⟩).tail.2 - i.val ≤ (c.side i).tail.2 ∧
    (c.side i).tail.2 ≤ (c.side ⟨0,hm⟩).tail.2 + i.val := by
  have : NeZero m := ⟨Nat.ne_of_gt hm⟩
  obtain ⟨i,hi⟩ := i
  induction i with
  | zero => simp
  | succ n ih =>
    have hn : n < m := by omega
    have hh := c.follows ⟨n,hn⟩
    have hr : finRotate m ⟨n,hn⟩ = ⟨n+1,hi⟩ := by
      apply Fin.ext
      simp only [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
      exact Nat.mod_eq_of_lt hi
    rw [hr, SquareSide.head] at hh
    have hx := congrArg Prod.fst hh
    have hy := congrArg Prod.snd hh
    have ihh := ih hn
    cases hd : (c.side ⟨n,hn⟩).2 <;>
      simp [hd,Step.delta] at hx hy <;> dsimp only at * <;> omega

/-- With the source's length m, every enclosing loop has a permitted starting
point in a deterministic box of cardinality (2m+3)^2. -/
theorem start_mem_box (c : SquareLoop m) (hm : 0 < m) (hc : c.winding ≠ 0) :
    (c.side ⟨0,hm⟩).tail ∈ orientedSelectionBox (m+1) := by
  obtain ⟨⟨i,hi⟩,⟨j,hj0,hj1,hj2⟩⟩ := c.winding_locations hc
  have hbi := c.tail_bounds hm i
  have hbj := c.tail_bounds hm j
  have hi' := i.isLt
  have hj' := j.isLt
  simp only [orientedSelectionBox, mem_product, mem_Icc]
  constructor <;> constructor <;> omega

end SquareLoop

end PlanarFPP

end OAI
