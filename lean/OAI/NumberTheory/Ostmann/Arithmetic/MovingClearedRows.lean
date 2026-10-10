import OAI.NumberTheory.Ostmann.Arithmetic.MovingOccurrenceNumerator

namespace OAI

/-! # Exact cleared rows before reduction modulo prime squares

The row identities hold over the integers before any division or reduction.
This permits the same occurrence line to be used modulo a prime square.
-/

namespace Ostmann
open scoped Classical

namespace PolynomialGiantRows

theorem cleared_movingReverse {σ R : Type*} [CommRing R]
    (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* R)
    (left : Bool) (v w u : MvPolynomial σ ℤ) (x y L H p : R)
    (hL : φ T.rows.a * x + φ T.rows.b * y = φ T.denominator * L)
    (hH : φ T.rows.c * x + φ T.rows.d * y = φ T.denominator * H)
    (hp : φ v * H - φ w * L = φ u * p) :
    let S := T.movingReverse left v w u
    φ S.rows.a * x + φ S.rows.b * y = φ S.denominator * p ∧
      φ S.rows.c * x + φ S.rows.d * y =
        φ S.denominator * (if left then L else H) := by
  have hnew : φ (v * T.rows.c - w * T.rows.a) * x +
      φ (v * T.rows.d - w * T.rows.b) * y = φ (T.denominator * u) * p := by
    simp only [map_sub, map_mul]
    linear_combination φ v * hH - φ w * hL + φ T.denominator * hp
  have hkeepL : φ (u * T.rows.a) * x + φ (u * T.rows.b) * y =
      φ (T.denominator * u) * L := by
    simp only [map_mul]
    linear_combination φ u * hL
  have hkeepH : φ (u * T.rows.c) * x + φ (u * T.rows.d) * y =
      φ (T.denominator * u) * H := by
    simp only [map_mul]
    linear_combination φ u * hH
  cases left
  · exact ⟨hnew, hkeepH⟩
  · exact ⟨hnew, hkeepL⟩

end PolynomialGiantRows

/-- The actual natural path multiplied by the cleared denominator equals
its polynomial rows over any ring, in particular over `ℤ` and `ZMod (p²)`. -/
theorem movingSlotNaturalPath_cleared {σ R : Type*} [CommRing R]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ)) (pair : ℕ × ℕ)
    (hvalid : MovingSlotPathIntegral value path pair) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
    let T := movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)
    let out := movingSlotNaturalPath value path pair
    φ T.rows.a * (pair.1 : R) + φ T.rows.b * (pair.2 : R) =
        φ T.denominator * (out.1 : R) ∧
      φ T.rows.c * (pair.1 : R) + φ T.rows.d * (pair.2 : R) =
        φ T.denominator * (out.2 : R) := by
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
  induction path with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity,
      GiantRows.identity, movingSlotNaturalPath]
  | cons s path ih =>
    let out := movingSlotNaturalPath value path pair
    have he : φ s.polynomial.v * (out.2 : R) - φ s.polynomial.w * (out.1 : R) =
        φ s.polynomial.u * (s.naturalPivot value out.1 out.2 : R) := by
      have hc := congrArg (fun z : ℤ => (z : R)) hvalid.2.2
      simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul] at hc
      simp only [φ, MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval]
      convert hc using 1 <;> ring
    have h := PolynomialGiantRows.cleared_movingReverse
      (movingPolynomialAncestors (path.map MovingSlotReversal.polynomial)) φ
      s.left s.polynomial.v s.polynomial.w s.polynomial.u
      (pair.1 : R) (pair.2 : R) (out.1 : R) (out.2 : R)
      (s.naturalPivot value out.1 out.2 : R) (ih hvalid.1).1 (ih hvalid.1).2 he
    cases hleft : s.left <;>
      simpa only [List.map_cons, movingPolynomialAncestors, movingSlotNaturalPath,
        MovingSlotReversal.naturalStep, MovingSlotReversal.polynomial, hleft, Bool.false_eq_true, ite_false, ite_true, out] using h

/-- The single cleared line is the exact current numerator times the
ancestor denominator. No unit or primality hypotheses enter this identity. -/
theorem movingSlotLine_cleared_numerator {σ R : Type*} [CommRing R]
    (value : σ → ℕ) (path : List (MovingSlotReversal σ))
    (current : MovingSlotReversal σ) (XL XR : ℕ)
    (hvalid : MovingSlotPathIntegral value path (XL, XR)) :
    let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
    let pair := movingSlotNaturalPath value path (XL, XR)
    φ (movingSlotLine path current).a * (XL : R) +
      φ (movingSlotLine path current).b * (XR : R) =
        φ (movingSlotLine path current).denominator *
          ((current.leftFrequency : R) *
              ((pair.2 * MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : R) -
            (current.rightFrequency : R) *
              ((pair.1 * MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : R)) := by
  let φ := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => (value i : R))
  have h := movingSlotNaturalPath_cleared (R := R) value path (XL, XR) hvalid
  change φ _ * (XL : R) + φ _ * (XR : R) = _
  simp only [movingSlotLine, movingHistoryLine, PolynomialGiantRows.numeratorLine,
    map_sub, map_mul]
  have he : φ current.polynomial.v *
      ((movingSlotNaturalPath value path (XL, XR)).2 : R) -
      φ current.polynomial.w * ((movingSlotNaturalPath value path (XL, XR)).1 : R) =
      (current.leftFrequency : R) *
        (((movingSlotNaturalPath value path (XL, XR)).2 *
          MovingSlotReversal.naturalProduct value current.rightSlots : ℕ) : R) -
      (current.rightFrequency : R) *
        (((movingSlotNaturalPath value path (XL, XR)).1 *
          MovingSlotReversal.naturalProduct value current.leftSlots : ℕ) : R) := by
    simp only [φ, MovingSlotReversal.polynomial, MovingSlotReversal.coefficient_nat_eval,
      Nat.cast_mul]
    ring
  rw [← he]
  linear_combination φ current.polynomial.v * h.2 - φ current.polynomial.w * h.1

end Ostmann

end OAI
