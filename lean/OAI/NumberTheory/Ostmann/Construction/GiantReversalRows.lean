import Mathlib.Tactic.Ring
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLifts

namespace OAI

/-! # Coefficient rows of the giant reversals

At a reversal one current giant is retained and the other becomes
`(v * Hminus - w * Hplus) / u`, with all three coefficients units modulo
the internal prime. The two current giants remain independent linear
forms in the top giants, so every subsequent numerator is a nonzero row.
-/

namespace Ostmann

/-- Coefficients of the two current giants in the two top giants. -/
@[ext] structure GiantRows (R : Type*) where
  a : R
  b : R
  c : R
  d : R

namespace GiantRows

variable {R : Type*} [CommRing R]

def identity : GiantRows R := ⟨1, 0, 0, 1⟩

def det (T : GiantRows R) : R := T.a * T.d - T.b * T.c

def eval (T : GiantRows R) (x y : R) : R × R :=
  (T.a * x + T.b * y, T.c * x + T.d * y)

/-- `left = true` retains the first giant; `false` retains the second. -/
def reverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) : GiantRows R :=
  if left then
    ⟨T.a, T.b, (u⁻¹ : Rˣ) * ((v : R) * T.c - (w : R) * T.a),
      (u⁻¹ : Rˣ) * ((v : R) * T.d - (w : R) * T.b)⟩
  else
    ⟨(u⁻¹ : Rˣ) * ((v : R) * T.c - (w : R) * T.a),
      (u⁻¹ : Rˣ) * ((v : R) * T.d - (w : R) * T.b), T.c, T.d⟩

theorem eval_reverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) (x y : R) :
    (T.reverse left v w u).eval x y =
      if left then ((T.eval x y).1,
        (u⁻¹ : Rˣ) * ((v : R) * (T.eval x y).2 - (w : R) * (T.eval x y).1))
      else ((u⁻¹ : Rˣ) * ((v : R) * (T.eval x y).2 - (w : R) * (T.eval x y).1),
        (T.eval x y).2) := by
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, ite_true, eval]
  · congr 1
    ring
  · congr 1
    ring

theorem det_reverse (T : GiantRows R) (left : Bool) (v w u : Rˣ) :
    (T.reverse left v w u).det =
      (if left then (u⁻¹ : Rˣ) * (v : R) else -(u⁻¹ : Rˣ) * (w : R)) * T.det := by
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, ite_true, det] <;> ring

theorem isUnit_det_reverse (T : GiantRows R) (hT : IsUnit T.det)
    (left : Bool) (v w u : Rˣ) : IsUnit (T.reverse left v w u).det := by
  rw [det_reverse]
  apply IsUnit.mul _ hT
  cases left
  · exact (u⁻¹).isUnit.neg.mul w.isUnit
  · exact (u⁻¹).isUnit.mul v.isUnit

/-- Every numerator in an invertible current pair is a nonzero row. -/
theorem numerator_nonzero {K : Type*} [Field K] (T : GiantRows K)
    (hT : T.det ≠ 0) (v w : Kˣ) :
    (v : K) * T.c - (w : K) * T.a ≠ 0 ∨
      (v : K) * T.d - (w : K) * T.b ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨ha, hb⟩ := h
  have he : (v : K) * T.det = 0 := by
    dsimp [det]
    linear_combination T.a * hb - T.b * ha
  exact mul_ne_zero (Units.ne_zero v) hT he

end GiantRows

/-- The data retained at one ancestor substitution. -/
structure GiantReversal (R : Type*) [CommRing R] where
  left : Bool
  v : Rˣ
  w : Rˣ
  u : Rˣ

def giantAncestorRows {R : Type*} [CommRing R] : List (GiantReversal R) → GiantRows R
  | [] => GiantRows.identity
  | s :: steps => (giantAncestorRows steps).reverse s.left s.v s.w s.u

theorem giantAncestorRows_isUnit_det {R : Type*} [CommRing R]
    (steps : List (GiantReversal R)) : IsUnit (giantAncestorRows steps).det := by
  induction steps with
  | nil => simp [giantAncestorRows, GiantRows.identity, GiantRows.det]
  | cons s steps ih => exact GiantRows.isUnit_det_reverse _ ih s.left s.v s.w s.u

theorem giantAncestorRows_numerator_nonzero {p : ℕ} [Fact p.Prime]
    (steps : List (GiantReversal (ZMod p))) (v w : (ZMod p)ˣ) :
    (v : ZMod p) * (giantAncestorRows steps).c -
      (w : ZMod p) * (giantAncestorRows steps).a ≠ 0 ∨
    (v : ZMod p) * (giantAncestorRows steps).d -
      (w : ZMod p) * (giantAncestorRows steps).b ≠ 0 :=
  GiantRows.numerator_nonzero _ (giantAncestorRows_isUnit_det steps).ne_zero v w

end Ostmann

end OAI
