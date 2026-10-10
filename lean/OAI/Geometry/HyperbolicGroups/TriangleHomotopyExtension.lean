import Mathlib
import OAI.Geometry.HyperbolicGroups.TriangleSquare
import OAI.Geometry.HyperbolicGroups.SquareBoundaryExtension

namespace OAI

/-! Exact homotopy extension on a genuine closed triangle, retaining all
three side tracks and collapsing the fourth square side throughout. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.TriangleHomotopyExtension
open TriangleSquare SquareBoundaryExtension
variable {X : Type*} [TopologicalSpace X]

def pairCube : C((Fin 2 → I),I × I) := ⟨Homeomorph.finTwoArrow,Homeomorph.finTwoArrow.continuous⟩
def cubePair : C(I × I,(Fin 2 → I)) := ⟨Homeomorph.finTwoArrow.symm,Homeomorph.finTwoArrow.symm.continuous⟩

variable (f : C(Triangle,X)) (D : Data (X := X))
  (hf : ∀ q (z : Fin 2 → I), z q.1 = endpoint q.2 →
    D.side q (0,z (other q.1)) = f (quotient (pairCube z)))
  (ht : ∀ t s, D.side (1,true) (t,s) = D.side (1,true) (t,0))

def square : C(I × (I × I),X) :=
  (D.extend (f.comp (quotient.comp pairCube)) hf).comp
    ((ContinuousMap.id I).prodMap cubePair)

lemma square_edge (q : Fin 2 × Bool) (t : I) (z : I × I)
    (hz : cubePair z q.1 = endpoint q.2) :
    square f D hf (t,z) = D.side q (t,cubePair z (other q.1)) :=
  D.extend_edge _ hf q t (cubePair z) hz

lemma square_initial (z : I × I) : square f D hf (0,z) = f (quotient z) := by
  change D.extend _ hf (0,cubePair z) = _
  rw [D.extend_initial]
  rfl

lemma square_top (t s : I) : square f D hf (t,(s,1)) = D.side (1,true) (t,s) :=
  square_edge f D hf (1,true) t (s,1) rfl

include ht in
lemma square_top_const (t s : I) : square f D hf (t,(s,1)) = square f D hf (t,(0,1)) := by
  rw [square_top,square_top,ht]

def extend : C(I × Triangle,X) := TriangleSquare.descend (square f D hf) (square_top_const f D hf ht)

lemma extend_square (t : I) (z : I × I) : extend f D hf ht (t,quotient z) = square f D hf (t,z) :=
  TriangleSquare.descend_quotient _ _ t z

lemma extend_initial (z : Triangle) : extend f D hf ht (0,z) = f z := by
  obtain ⟨z,rfl⟩ := quotient_surjective z
  rw [extend_square,square_initial]
lemma extend_bottom (t s : I) : extend f D hf ht (t,quotient (s,0)) = D.side (1,false) (t,s) := by
  rw [extend_square]
  exact square_edge f D hf (1,false) t (s,0) rfl
lemma extend_left (t s : I) : extend f D hf ht (t,quotient (0,s)) = D.side (0,false) (t,s) := by
  rw [extend_square]
  exact square_edge f D hf (0,false) t (0,s) rfl
lemma extend_right (t s : I) : extend f D hf ht (t,quotient (1,s)) = D.side (0,true) (t,s) := by
  rw [extend_square]
  exact square_edge f D hf (0,true) t (1,s) rfl
lemma extend_top (t s : I) : extend f D hf ht (t,quotient (s,1)) = D.side (1,true) (t,s) := by
  rw [extend_square,square_top]

end HyperbolicObstruction.TriangleHomotopyExtension
end

end OAI
