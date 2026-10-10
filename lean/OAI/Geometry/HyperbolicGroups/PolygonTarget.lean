import Mathlib
import OAI.Geometry.HyperbolicGroups.NormalCell

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

namespace PolygonTarget
variable {C L V A : Type*} [AddCommGroup A]

/-- An actual finite closed edge boundary for each cell, with indexed sides.
The cell type may be infinite (as in the universal cover); every cell boundary
is finite. Orientation reversal is constructed, not postulated. -/
structure Boundary (C : Type*) (L : Type*) (V : Type*) where
  size : C → ℕ
  positive : ∀ c, 0 < size c
  label : (c : C) → Fin (size c) → L
  start : L → V
  rev : L → L
  inv : ∀ l, rev (rev l) = l
  closed : ∀ c i, start (label c (finRotate (size c) i)) = start (rev (label c i))

namespace Boundary
variable (B : Boundary C L V)
abbrev Side := Σ c : C, Bool × Fin (B.size c)

def next : Perm B.Side where
  toFun s := ⟨s.1,s.2.1,if s.2.1 then finRotate (B.size s.1) s.2.2 else (finRotate (B.size s.1))⁻¹ s.2.2⟩
  invFun s := ⟨s.1,s.2.1,if s.2.1 then (finRotate (B.size s.1))⁻¹ s.2.2 else finRotate (B.size s.1) s.2.2⟩
  left_inv := by rintro ⟨c,b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]
  right_inv := by rintro ⟨c,b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]

def opposite : Perm B.Side where
  toFun s := ⟨s.1,!s.2.1,s.2.2⟩
  invFun s := ⟨s.1,!s.2.1,s.2.2⟩
  left_inv := by rintro ⟨c,b,i⟩; cases b <;> rfl
  right_inv := by rintro ⟨c,b,i⟩; cases b <;> rfl

def sideLabel (s : B.Side) : L := if s.2.1 then B.label s.1 s.2.2 else B.rev (B.label s.1 s.2.2)

def weight (w : C → A) (s : B.Side) : A := if s.2.1 then w s.1 else -(w s.1)

lemma opposite_sq : B.opposite * B.opposite = 1 := by
  apply Equiv.ext
  rintro ⟨c,b,i⟩; cases b <;> rfl

lemma reverse_next (s : B.Side) : B.opposite (B.next s) = B.next⁻¹ (B.opposite s) := by
  rcases s with ⟨c,b,i⟩; cases b <;> rfl

lemma orientation_next (s : B.Side) : (B.next s).2.1 = s.2.1 := rfl

lemma orientation_cycle {s t : B.Side} (h : B.next.SameCycle s t) : s.2.1 = t.2.1 := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm Bool)) (j := fun s : B.Side => s.2.1) B.orientation_next h)

lemma opposite_cycle (s : B.Side) : ¬ B.next.SameCycle s (B.opposite s) := by
  intro h
  have hh := B.orientation_cycle h
  rcases s with ⟨c,b,i⟩; cases b <;> cases hh

lemma edge_opposite (s : B.Side) : B.sideLabel (B.opposite s) = B.rev (B.sideLabel s) := by
  rcases s with ⟨c,b,i⟩; cases b <;> simp [sideLabel,opposite,B.inv]

lemma next_start (s : B.Side) : B.start (B.sideLabel (B.next s)) = B.start (B.rev (B.sideLabel s)) := by
  rcases s with ⟨c,b,i⟩
  let : NeZero (B.size c) := ⟨Nat.ne_of_gt (B.positive c)⟩
  cases b with
  | false =>
    simpa [sideLabel,next,B.inv] using (B.closed c ((finRotate (B.size c))⁻¹ i)).symm
  | true => exact B.closed c i

lemma weight_next (w : C → A) (s : B.Side) : B.weight w (B.next s) = B.weight w s := rfl

lemma weight_opposite (w : C → A) (s : B.Side) : B.weight w s + B.weight w (B.opposite s) = 0 := by
  rcases s with ⟨c,b,i⟩; cases b <;> simp [weight,opposite]

/-- The exact indexed oriented cell target constructed from ordinary polygon
boundaries, suitable for `CellPicture.normalize`. -/
def target (w : C → A) (apex : V → Bool)
    (hr : ∀ l, apex (B.start l) = true → apex (B.start (B.rev l)) = false) :
    CellTarget B.Side L V A where
  next := B.next
  opposite := B.opposite
  opposite_sq := B.opposite_sq
  reverse_next := B.reverse_next
  opposite_cycle := B.opposite_cycle
  edge := B.sideLabel
  start := B.start
  rev := B.rev
  rev_rev := B.inv
  edge_opposite := B.edge_opposite
  next_start := B.next_start
  apex := apex
  radial := fun s => hr (B.sideLabel s)
  weight := B.weight w
  weight_next := B.weight_next w
  weight_opposite := B.weight_opposite w

end Boundary
end PolygonTarget

namespace CellTarget
variable {S L V A D : Type*} [AddCommMonoid A]
variable (T : CellTarget S L V A)

/-- For genuine closed target cell boundaries, vertex-map compatibility
follows from indexed face maps and the literal opposite-edge labels. -/
theorem respects_of_edge (M : PictureMap D) (j : D → S)
    (hj : IndexedFaceMap M.face T.next j)
    (he : ∀ x, T.edge (j (M.edge x)) = T.rev (T.edge (j x))) :
    M.Respects (T.edge ∘ j) T.start T.rev := by
  constructor
  · intro x
    change T.start (T.edge (j (M.face (M.edge x)))) = T.start (T.edge (j x))
    rw [hj.commute,T.next_start,he,T.rev_rev]
  · exact he

end CellTarget
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
