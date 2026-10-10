import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyResidues

namespace OAI

/-! # Composition of the cleared occurrence lines

The identity works before any descendant division. It lets the current
internal-prime congruence establish integrality inductively, without assuming
the conclusion for the rest of the path.
-/

namespace Ostmann
open scoped Classical

noncomputable def PolynomialGiantRows.evalNumerator {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R) (x y : R) : R × R :=
  (φ T.rows.a * x + φ T.rows.b * y, φ T.rows.c * x + φ T.rows.d * y)

theorem PolynomialGiantRows.evalNumerator_movingReverse {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R)
    (left : Bool) (v w u : MvPolynomial σ ℤ) (x y : R) :
    (T.movingReverse left v w u).evalNumerator φ x y =
      (φ v * (T.evalNumerator φ x y).2 - φ w * (T.evalNumerator φ x y).1,
        φ u * (if left then (T.evalNumerator φ x y).1 else (T.evalNumerator φ x y).2)) := by
  cases left <;> apply Prod.ext <;>
    simp only [evalNumerator, movingReverse, reverse, swap, GiantRows.swap,
      Bool.false_eq_true, ite_false, ite_true, map_mul, map_sub] <;> ring

theorem movingPolynomialAncestors_append_eval {σ R : Type*} [CommRing R]
    (φ : MvPolynomial σ ℤ →+* R) (a b : List (PolynomialReversal σ)) (x y : R) :
    (movingPolynomialAncestors (a ++ b)).evalNumerator φ x y =
      (movingPolynomialAncestors a).evalNumerator φ
        ((movingPolynomialAncestors b).evalNumerator φ x y).1
        ((movingPolynomialAncestors b).evalNumerator φ x y).2 := by
  induction a with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.evalNumerator,
      PolynomialGiantRows.identity, GiantRows.identity]
  | cons s a ih =>
    simp only [List.cons_append, movingPolynomialAncestors,
      PolynomialGiantRows.evalNumerator_movingReverse, ih]

theorem PolynomialGiantRows.evalNumerator_smul {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R) (c x y : R) :
    T.evalNumerator φ (c * x) (c * y) =
      (c * (T.evalNumerator φ x y).1, c * (T.evalNumerator φ x y).2) := by
  apply Prod.ext <;> simp only [evalNumerator] <;> ring

theorem movingSlotLine_eval {σ R : Type*} [CommRing R]
    (φ : MvPolynomial σ ℤ →+* R) (path : List (MovingSlotReversal σ))
    (s : MovingSlotReversal σ) (x y : R) :
    φ (movingSlotLine path s).a * x + φ (movingSlotLine path s).b * y =
      φ s.polynomial.v * ((movingPolynomialAncestors
        (path.map MovingSlotReversal.polynomial)).evalNumerator φ x y).2 -
      φ s.polynomial.w * ((movingPolynomialAncestors
        (path.map MovingSlotReversal.polynomial)).evalNumerator φ x y).1 := by
  simp only [movingSlotLine, movingHistoryLine, PolynomialGiantRows.numeratorLine,
    PolynomialGiantRows.evalNumerator, map_mul, map_sub]
  ring

/-- A root division multiplies every descendant cleared line by its root
denominator. No integrality of the descendant path is needed. -/
theorem movingSlotLine_append_singleton {σ R : Type*} [CommRing R]
    (φ : MvPolynomial σ ℤ →+* R) (path : List (MovingSlotReversal σ))
    (current root : MovingSlotReversal σ) (x y p : R)
    (hroot : φ root.polynomial.v * y - φ root.polynomial.w * x = φ root.polynomial.u * p) :
    φ (movingSlotLine (path ++ [root]) current).a * x +
        φ (movingSlotLine (path ++ [root]) current).b * y =
      φ root.polynomial.u * (φ (movingSlotLine path current).a * p +
        φ (movingSlotLine path current).b * (if root.left then x else y)) := by
  rw [movingSlotLine_eval, movingSlotLine_eval, List.map_append,
    movingPolynomialAncestors_append_eval]
  have he : (movingPolynomialAncestors ([root].map MovingSlotReversal.polynomial)).evalNumerator φ x y =
      (φ root.polynomial.u * p, φ root.polynomial.u * (if root.left then x else y)) := by
    rw [List.map_cons, List.map_nil, movingPolynomialAncestors,
      PolynomialGiantRows.evalNumerator_movingReverse]
    simp only [MovingSlotReversal.polynomial] at hroot
    simp only [movingPolynomialAncestors, PolynomialGiantRows.evalNumerator,
      PolynomialGiantRows.identity, GiantRows.identity, map_one, map_zero,
      one_mul, zero_mul, add_zero, zero_add, MovingSlotReversal.polynomial, hroot]
  rw [he, PolynomialGiantRows.evalNumerator_smul]
  simp only
  ring

theorem movingSlotLine_append_singleton_zero_iff {σ : Type*} {q : ℕ} [Fact q.Prime]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current root : MovingSlotReversal σ) (x y p : ℤ)
    (hroot : root.signedNumerator value x y =
      root.rootFrequency * (MovingSlotReversal.naturalProduct value root.compensationSlots : ℤ) * p)
    (hu : MovingSlotReversal.naturalReduction q value root.polynomial.u ≠ 0) :
    let φ := MovingSlotReversal.naturalReduction q value
    φ (movingSlotLine (path ++ [root]) current).a * (x : ZMod q) +
        φ (movingSlotLine (path ++ [root]) current).b * (y : ZMod q) = 0 ↔
      φ (movingSlotLine path current).a * (p : ZMod q) +
        φ (movingSlotLine path current).b * ((if root.left then x else y : ℤ) : ZMod q) = 0 := by
  have hc := congrArg (fun z : ℤ => (z : ZMod q)) hroot
  simp only [MovingSlotReversal.signedNumerator, Int.cast_sub, Int.cast_mul,
    Int.cast_natCast] at hc
  have hh : MovingSlotReversal.naturalReduction q value root.polynomial.v * (y : ZMod q) -
      MovingSlotReversal.naturalReduction q value root.polynomial.w * (x : ZMod q) =
      MovingSlotReversal.naturalReduction q value root.polynomial.u * (p : ZMod q) := by
    simp only [MovingSlotReversal.naturalReduction, MovingSlotReversal.polynomial,
      MovingSlotReversal.coefficient_nat_eval]
    linear_combination hc
  have he := movingSlotLine_append_singleton (MovingSlotReversal.naturalReduction q value)
    path current root (x : ZMod q) (y : ZMod q) (p : ZMod q) hh
  dsimp only
  rw [he, mul_eq_zero, or_iff_right hu]
  cases root.left <;> rfl

end Ostmann

end OAI
