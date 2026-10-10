import Mathlib
import OAI.Geometry.HyperbolicGroups.TriangleSquare
import OAI.Geometry.HyperbolicGroups.BasedSquareContraction

namespace OAI

/-! The actual triangular pi2 obstruction has a literal contracting prism
when the three oriented edge corrections have the prescribed coboundary. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.BasedTriangleContraction
open TriangleSquare HSpacePathObstruction
variable {X : Type*} [TopologicalSpace X] (b : X)
local notation "e" => Path.refl b
variable (f : C(Triangle,X))
  (hb : ∀ s, f (quotient (s,0)) = b)
  (hl : ∀ s, f (quotient (0,s)) = b)
  (hr : ∀ s, f (quotient (1,s)) = b)

include hr in
lemma top_const (s : I) : f (quotient (s,1)) = b := by
  rw [quotient_one,←quotient_one (1 : I)]
  exact hr 1

def theta : FundamentalGroup (Path b b) e :=
  BasedSquareContraction.faceObstruction b (p:=e) (q:=e) (r:=e) (s:=e) (f.comp quotient) hb hl hr (top_const b f hr)
    (Path.refl e) (Path.refl e) (Path.refl e) (Path.refl e)

variable (u01 u02 u12 : Path (Path.refl b) (Path.refl b))
  (hu : loopClass u02 * theta b f hb hl hr = loopClass u01 * loopClass u12)

lemma corrected_zero (hu : loopClass u02 * theta b f hb hl hr = loopClass u01 * loopClass u12) :
    BasedSquareContraction.faceObstruction b (p:=e) (q:=e) (r:=e) (s:=e) (f.comp quotient) hb hl hr (top_const b f hr)
      ((Path.refl e).trans u01) ((Path.refl e).trans u02)
      ((Path.refl e).trans u12) ((Path.refl e).trans (Path.refl e)) = 1 := by
  unfold BasedSquareContraction.faceObstruction
  rw [correction]
  have he : loopClass (Path.refl e) = 1 := rfl
  rw [he,mul_one]
  change (loopClass u02 * theta b f hb hl hr) * (loopClass u01 * loopClass u12)⁻¹ = 1
  rw [hu,mul_inv_cancel]

def square : C(I × (I × I),X) :=
  BasedSquareContraction.contraction b (p:=e) (q:=e) (r:=e) (s:=e) (f.comp quotient) hb hl hr (top_const b f hr)
    ((Path.refl e).trans u01) ((Path.refl e).trans u02)
    ((Path.refl e).trans u12) ((Path.refl e).trans (Path.refl e))
    (corrected_zero b f hb hl hr u01 u02 u12 hu)

lemma square_top (t s : I) : square b f hb hl hr u01 u02 u12 hu (t,(s,1)) = b := by
  calc
    _ = ((Path.refl e).trans (Path.refl e)) t s :=
      BasedSquareContraction.contraction_top b (p := e) (q := e) (r := e) (s := e)
        (f.comp quotient) hb hl hr (top_const b f hr)
        ((Path.refl e).trans u01) ((Path.refl e).trans u02)
        ((Path.refl e).trans u12) ((Path.refl e).trans (Path.refl e))
        (corrected_zero b f hb hl hr u01 u02 u12 hu) t s
    _ = b := congrArg (fun p : Path e e => p t s) Path.refl_trans_refl

def contraction : C(I × Triangle,X) := TriangleSquare.descend
  (square b f hb hl hr u01 u02 u12 hu)
  (fun t s => (square_top b f hb hl hr u01 u02 u12 hu t s).trans
    (square_top b f hb hl hr u01 u02 u12 hu t 0).symm)

lemma contraction_initial (z : Triangle) : contraction b f hb hl hr u01 u02 u12 hu (0,z) = f z := by
  obtain ⟨z,rfl⟩ := quotient_surjective z
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_initial _ _ _ _ _ _ _ _ _ _ _ z
lemma contraction_final (z : Triangle) : contraction b f hb hl hr u01 u02 u12 hu (1,z) = b := by
  obtain ⟨z,rfl⟩ := quotient_surjective z
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_final _ _ _ _ _ _ _ _ _ _ _ z
lemma contraction_bottom (t s : I) :
    contraction b f hb hl hr u01 u02 u12 hu (t,quotient (s,0)) = ((Path.refl e).trans u01) t s := by
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_bottom _ _ _ _ _ _ _ _ _ _ _ t s
lemma contraction_left (t s : I) :
    contraction b f hb hl hr u01 u02 u12 hu (t,quotient (0,s)) = ((Path.refl e).trans u02) t s := by
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_left _ _ _ _ _ _ _ _ _ _ _ t s
lemma contraction_right (t s : I) :
    contraction b f hb hl hr u01 u02 u12 hu (t,quotient (1,s)) = ((Path.refl e).trans u12) t s := by
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_right _ _ _ _ _ _ _ _ _ _ _ t s

end HyperbolicObstruction.BasedTriangleContraction
end

end OAI
