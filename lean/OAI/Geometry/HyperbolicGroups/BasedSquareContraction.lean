import Mathlib
import OAI.Geometry.HyperbolicGroups.HSpacePathObstruction
import OAI.Geometry.HyperbolicGroups.PathHomotopyTopology
import OAI.Geometry.HyperbolicGroups.ParameterizedSquareFilling

namespace OAI

/-! A vanishing actual pi-2 obstruction constructs a continuous square
contraction with four independently prescribed edge contractions. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.BasedSquareContraction
open HSpacePathObstruction
variable {X : Type*} [TopologicalSpace X] (b : X)
variable {p q r s : Path b b}
variable (f : C(I × I,X))
  (hb : ∀ x, f (x,0) = p x) (hl : ∀ x, f (0,x) = q x)
  (hr : ∀ x, f (1,x) = r x) (ht : ∀ x, f (x,1) = s x)

def facePath : Path (p.trans r) (q.trans s) :=
  PathHomotopyTopology.fromHomotopy (SquarePathFilling.unfill f hb hl hr ht)

variable (hp : Path p (Path.refl b)) (hq : Path q (Path.refl b)) (hr' : Path r (Path.refl b)) (hs : Path s (Path.refl b))

def faceObstruction : FundamentalGroup (Path b b) (Path.refl b) :=
  obstruction (facePath b f hb hl hr ht) hp hr' hq hs

variable (hz : faceObstruction b f hb hl hr ht hp hq hr' hs = 1)

def loopSquare : C(I × I,Path b b) :=
  SquarePathFilling.fill
    ((obstruction_vanishes_iff (facePath b f hb hl hr ht) hp hr' hq hs).mp hz).some

@[simp] lemma loopSquare_bottom (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (t,0) = (hp t).trans (hr' t) :=
  SquarePathFilling.fill_bottom _ t
@[simp] lemma loopSquare_top (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (t,1) = (hq t).trans (hs t) :=
  SquarePathFilling.fill_top _ t
@[simp] lemma loopSquare_left (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (0,t) = facePath b f hb hl hr ht t :=
  SquarePathFilling.fill_left _ t
@[simp] lemma loopSquare_right (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (1,t) = Path.refl b :=
  SquarePathFilling.fill_right _ t

/-- Literal face homotopy. Its domain is the actual closed square prism. -/
def contraction : C(I × (I × I),X) :=
  SquarePathFilling.paramFill b (loopSquare b f hb hl hr ht hp hq hr' hs hz)

@[simp] lemma contraction_initial (z : I × I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (0,z) = f z := by
  obtain ⟨z,rfl⟩ := SquarePathFilling.quotient_surjective z
  unfold contraction
  rw [SquarePathFilling.paramFill_quotient,loopSquare_left]
  rfl
@[simp] lemma contraction_final (z : I × I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (1,z) = b := by
  obtain ⟨z,rfl⟩ := SquarePathFilling.quotient_surjective z
  unfold contraction
  rw [SquarePathFilling.paramFill_quotient,loopSquare_right]
  rfl
@[simp] lemma contraction_bottom (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(x,0)) = hp t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_bottom x,SquarePathFilling.paramFill_quotient,loopSquare_bottom]
  exact SquarePathFilling.trans_half _ _ x
@[simp] lemma contraction_right (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(1,x)) = hr' t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_right x,SquarePathFilling.paramFill_quotient,loopSquare_bottom]
  exact SquarePathFilling.trans_upper _ _ x
@[simp] lemma contraction_left (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(0,x)) = hq t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_left x,SquarePathFilling.paramFill_quotient,loopSquare_top]
  exact SquarePathFilling.trans_half _ _ x
@[simp] lemma contraction_top (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(x,1)) = hs t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_top x,SquarePathFilling.paramFill_quotient,loopSquare_top]
  exact SquarePathFilling.trans_upper _ _ x

end HyperbolicObstruction.BasedSquareContraction
end

end OAI
