import OAI.Probability.GammaPassage.ContourCounts
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod

namespace OAI

/-! The uncancelled, counterclockwise square sides in
crossings.tex:cr:oriented-paths. A dual vertex `p` represents the actual
point `p - (1/2,1/2)`, so the square at the primal site `q` has lower-left
corner `q` in these integer coordinates. -/
namespace PlanarFPP
open Finset

instance : Fintype Step where
  elems := {Step.east, Step.west, Step.north, Step.south}
  complete d := by cases d <;> simp

def Step.left : Step → Step
  | .east => .north | .north => .west | .west => .south | .south => .east

def Step.right : Step → Step
  | .east => .south | .south => .west | .west => .north | .north => .east

def Step.outward (d : Step) : Vertex := d.right.delta

def Step.corner : Step → Vertex
  | .east => (0,0) | .north => (1,0) | .west => (1,1) | .south => (0,1)

abbrev SquareSide := Vertex × Step

def SquareSide.tail (e : SquareSide) : Vertex := e.1 + e.2.corner

def SquareSide.head (e : SquareSide) : Vertex := e.tail + e.2.delta

def IsBoundarySide (S : Finset Vertex) (e : SquareSide) : Prop :=
  e.1 ∈ S ∧ e.1 + e.2.outward ∉ S

instance (S : Finset Vertex) (e : SquareSide) : Decidable (IsBoundarySide S e) :=
  inferInstanceAs (Decidable (_ ∧ _))

def boundarySides (S : Finset Vertex) : Finset SquareSide :=
  (S ×ˢ univ).filter (fun e => e.1 + e.2.outward ∉ S)

@[simp] theorem mem_boundarySides (S : Finset Vertex) (e : SquareSide) :
    e ∈ boundarySides S ↔ IsBoundarySide S e := by
  simp [boundarySides, IsBoundarySide]

/-- Follow the first uncancelled side counterclockwise around the arriving
corner. The two tests inspect the other two squares meeting that corner. -/
def boundaryNext (S : Finset Vertex) (e : SquareSide) : SquareSide :=
  let q := e.1
  let d := e.2
  let r := q + d.left.outward
  let t := r + d.outward
  if r ∉ S then (q,d.left) else if t ∉ S then (r,d) else (t,d.right)

def boundaryPrev (S : Finset Vertex) (e : SquareSide) : SquareSide :=
  let q := e.1
  let d := e.2
  let r := q + d.right.outward
  let t := r + d.outward
  if r ∉ S then (q,d.right) else if t ∉ S then (r,d) else (t,d.left)

theorem boundaryNext_boundary (S : Finset Vertex) (e : SquareSide)
    (he : IsBoundarySide S e) : IsBoundarySide S (boundaryNext S e) := by
  rcases e with ⟨⟨x,y⟩,d⟩
  unfold boundaryNext
  dsimp only
  split
  · cases d <;> simp_all [IsBoundarySide, Step.left, Step.outward, Step.right,
      Step.delta]
  · split
    · cases d <;> simp_all [IsBoundarySide, Step.left, Step.outward, Step.right,
        Step.delta]
    · cases d <;>
        simp_all [IsBoundarySide, Step.left, Step.outward, Step.right,
          Step.delta, Prod.mk_add_mk, add_assoc]

theorem boundaryNext_tail (S : Finset Vertex) (e : SquareSide) :
    (boundaryNext S e).tail = e.head := by
  rcases e with ⟨⟨x,y⟩,d⟩
  unfold boundaryNext
  dsimp only
  split
  · cases d <;> simp [SquareSide.tail, SquareSide.head, Step.corner,
      Step.left, Step.delta, Prod.mk_add_mk]
  · split <;> cases d <;>
      simp [SquareSide.tail, SquareSide.head, Step.corner, Step.left,
        Step.right, Step.outward, Step.delta, Prod.mk_add_mk]

theorem boundaryPrev_next (S : Finset Vertex) (e : SquareSide)
    (he : IsBoundarySide S e) : boundaryPrev S (boundaryNext S e) = e := by
  rcases e with ⟨⟨x,y⟩,d⟩
  unfold boundaryNext
  dsimp only
  split
  · cases d <;>
      simp_all [boundaryPrev, IsBoundarySide, Step.left, Step.right,
        Step.outward, Step.delta, Prod.mk_add_mk]
  · split <;> cases d <;>
      simp_all [boundaryPrev, IsBoundarySide, Step.left, Step.right,
        Step.outward, Step.delta, Prod.mk_add_mk, add_assoc]

abbrev BoundarySide (S : Finset Vertex) := {e // e ∈ boundarySides S}

def boundarySuccessor (S : Finset Vertex) (e : BoundarySide S) : BoundarySide S :=
  ⟨boundaryNext S e.val, (mem_boundarySides S _).mpr
    (boundaryNext_boundary S e.val ((mem_boundarySides S _).mp e.property))⟩

theorem boundarySuccessor_injective (S : Finset Vertex) :
    Function.Injective (boundarySuccessor S) := by
  intro e f h
  apply Subtype.ext
  have hh := congrArg (fun a : BoundarySide S => boundaryPrev S a.val) h
  simpa only [boundarySuccessor, boundaryPrev_next S e.val
    ((mem_boundarySides S _).mp e.property), boundaryPrev_next S f.val
    ((mem_boundarySides S _).mp f.property)] using hh

/-- Cancellation of shared sides leaves a permutation of the remaining sides;
its cycles are directed closed walks with no repeated directed side. -/
noncomputable def boundaryPerm (S : Finset Vertex) : Equiv.Perm (BoundarySide S) :=
  Equiv.ofBijective (boundarySuccessor S)
    ⟨boundarySuccessor_injective S, Finite.surjective_of_injective
      (boundarySuccessor_injective S)⟩

@[simp] theorem boundaryPerm_tail (S : Finset Vertex) (e : BoundarySide S) :
    (boundaryPerm S e).val.tail = e.val.head := boundaryNext_tail S e.val

theorem boundaryPerm_ne_self (S : Finset Vertex) (e : BoundarySide S) :
    boundaryPerm S e ≠ e := by
  intro h
  have hh := boundaryPerm_tail S e
  rw [h] at hh
  have hz : e.val.2.delta = 0 := by
    have : e.val.tail + e.val.2.delta = e.val.tail + 0 := by
      simpa [SquareSide.head] using hh.symm
    exact add_left_cancel this
  cases hd : e.val.2 <;> simp [hd, Step.delta] at hz

/-- An unoriented dual edge cannot occur twice among uncancelled sides:
its two possible orientations have opposite occupied and unoccupied cells. -/
theorem boundary_dualEdge_injective (S : Finset Vertex) (e f : SquareSide)
    (he : IsBoundarySide S e) (hf : IsBoundarySide S f)
    (hh : e.2.edge e.tail = f.2.edge f.tail) : e = f := by
  rcases e with ⟨⟨x,y⟩,d⟩
  rcases f with ⟨⟨u,v⟩,a⟩
  cases d <;> cases a <;>
    simp_all [IsBoundarySide, SquareSide.tail, Step.edge, Step.corner,
      Step.outward, Step.right, Step.delta, Prod.mk_add_mk, Prod.ext_iff]

end PlanarFPP

end OAI
