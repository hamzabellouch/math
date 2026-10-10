import OAI.NumberTheory.Ostmann.Characters.PolynomialAncestorNonvanishing
import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantTree

namespace OAI

/-! # Ordered coefficient rows for the moving-giant reversal

In the manuscript's order both children put the inserted giant first. The
left child is therefore the exchanged version of the retained-first reversal.
This exchange preserves the nonvanishing determinant used in the line bounds.
-/

namespace Ostmann
namespace GiantRows

variable {R : Type*} [CommRing R]

def swap (T : GiantRows R) : GiantRows R := ⟨T.c, T.d, T.a, T.b⟩

@[simp] theorem eval_swap (T : GiantRows R) (x y : R) :
    T.swap.eval x y = ((T.eval x y).2, (T.eval x y).1) := rfl

theorem det_swap (T : GiantRows R) : T.swap.det = -T.det := by
  simp only [swap, det]
  ring

/-- Both source children order their giants as `(new, retained)`. -/
def movingReverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) : GiantRows R :=
  if left then (T.reverse true v w u).swap else T.reverse false v w u

theorem eval_movingReverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) (x y : R) :
    (T.movingReverse left v w u).eval x y =
      ((u⁻¹ : Rˣ) * ((v : R) * (T.eval x y).2 - (w : R) * (T.eval x y).1),
        if left then (T.eval x y).1 else (T.eval x y).2) := by
  cases left <;> simp only [movingReverse, Bool.false_eq_true, ite_false, ite_true,
    eval_swap, eval_reverse]

theorem isUnit_det_movingReverse (T : GiantRows R) (hT : IsUnit T.det)
    (left : Bool) (v w u : Rˣ) : IsUnit (T.movingReverse left v w u).det := by
  cases left
  · exact isUnit_det_reverse T hT false v w u
  · change IsUnit (T.reverse true v w u).swap.det
    rw [det_swap]
    exact (isUnit_det_reverse T hT true v w u).neg

/-- An exact integer node gives the actual child giant pair under reduction. -/
theorem movingReverse_integer_node {q : ℕ} [Fact q.Prime]
    (T : GiantRows (ZMod q)) (left : Bool) (v w u : (ZMod q)ˣ)
    (x y : ZMod q) (XL XR p CL CR ML MR comp : ℕ) (s fv fw : ℤ)
    (hpair : T.eval x y = ((XL : ZMod q), (XR : ZMod q)))
    (hv : (v : ZMod q) = (fv : ZMod q) * ((CR * MR : ℕ) : ZMod q))
    (hw : (w : ZMod q) = (fw : ZMod q) * ((CL * ML : ℕ) : ZMod q))
    (hu : (u : ZMod q) = (s : ZMod q) * (comp : ZMod q))
    (hnode : fv * ((XR * CR * MR : ℕ) : ℤ) -
      fw * ((XL * CL * ML : ℕ) : ℤ) = s * ((comp * p : ℕ) : ℤ)) :
    (T.movingReverse left v w u).eval x y =
      ((p : ZMod q), if left then (XL : ZMod q) else (XR : ZMod q)) := by
  have he : (v : ZMod q) * XR - (w : ZMod q) * XL = (u : ZMod q) * p := by
    have hc := congrArg (fun a : ℤ => (a : ZMod q)) hnode
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at hc
    rw [hv, hw, hu]
    simp only [Nat.cast_mul]
    convert hc using 1 <;> ring
  rw [eval_movingReverse, hpair]
  dsimp only
  rw [he, Units.val_inv_eq_inv_val, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero u), one_mul]

end GiantRows

/-- The full path retains the same determinant invariant in the source order. -/
def movingGiantAncestorRows {R : Type*} [CommRing R] : List (GiantReversal R) → GiantRows R
  | [] => GiantRows.identity
  | s :: steps => (movingGiantAncestorRows steps).movingReverse s.left s.v s.w s.u

theorem movingGiantAncestorRows_isUnit_det {R : Type*} [CommRing R]
    (steps : List (GiantReversal R)) : IsUnit (movingGiantAncestorRows steps).det := by
  induction steps with
  | nil => simp [movingGiantAncestorRows, GiantRows.identity, GiantRows.det]
  | cons s steps ih => exact GiantRows.isUnit_det_movingReverse _ ih _ _ _ _

theorem movingGiantAncestorRows_numerator_nonzero {q : ℕ} [Fact q.Prime]
    (steps : List (GiantReversal (ZMod q))) (v w : (ZMod q)ˣ) :
    (v : ZMod q) * (movingGiantAncestorRows steps).c -
        (w : ZMod q) * (movingGiantAncestorRows steps).a ≠ 0 ∨
      (v : ZMod q) * (movingGiantAncestorRows steps).d -
        (w : ZMod q) * (movingGiantAncestorRows steps).b ≠ 0 :=
  GiantRows.numerator_nonzero _ (movingGiantAncestorRows_isUnit_det steps).ne_zero v w

namespace PolynomialGiantRows

variable {σ : Type*}

noncomputable def swap (T : PolynomialGiantRows σ) : PolynomialGiantRows σ :=
  ⟨T.rows.swap, T.denominator⟩

noncomputable def movingReverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) : PolynomialGiantRows σ :=
  if left then (T.reverse true v w u).swap else T.reverse false v w u

@[simp] theorem normalized_swap {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) : T.swap.normalized φ = (T.normalized φ).swap := rfl

theorem normalized_movingReverse {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hd : φ T.denominator ≠ 0) (hv : φ v ≠ 0) (hw : φ w ≠ 0) (hu : φ u ≠ 0) :
    (T.movingReverse left v w u).normalized φ =
      (T.normalized φ).movingReverse left (Units.mk0 (φ v) hv) (Units.mk0 (φ w) hw)
        (Units.mk0 (φ u) hu) := by
  cases left <;> simp only [movingReverse, GiantRows.movingReverse, Bool.false_eq_true,
    ite_false, ite_true, normalized_swap, normalized_reverse T φ _ v w u hd hv hw hu]

theorem degreeLE_movingReverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) (d e : ℕ) (hT : T.DegreeLE d)
    (hv : v.totalDegree ≤ e) (hw : w.totalDegree ≤ e) (hu : u.totalDegree ≤ e) :
    (T.movingReverse left v w u).DegreeLE (d + e) := by
  have h := degreeLE_reverse T left v w u d e hT hv hw hu
  cases left
  · exact h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2⟩

end PolynomialGiantRows
end Ostmann

end OAI
