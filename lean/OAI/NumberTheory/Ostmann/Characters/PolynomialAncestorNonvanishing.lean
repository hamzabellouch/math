import OAI.NumberTheory.Ostmann.Characters.PolynomialGiantTests

namespace OAI

/-! # Nonvanishing of the actual normalized ancestor rows -/

namespace Ostmann

theorem polynomialAncestorRows_denominator_ne_zero {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.u ≠ 0) :
    φ (polynomialAncestorRows steps).denominator ≠ 0 := by
  induction steps with
  | nil => simp [polynomialAncestorRows, PolynomialGiantRows.identity]
  | cons s steps ih =>
    have ht := ih (fun t ht => h t (by simp [ht]))
    have hs := h s (by simp)
    have he : ((polynomialAncestorRows steps).reverse s.left s.v s.w s.u).denominator =
        (polynomialAncestorRows steps).denominator * s.u := by
      cases h : s.left <;> rfl
    change φ ((polynomialAncestorRows steps).reverse s.left s.v s.w s.u).denominator ≠ 0
    rw [he, map_mul]
    exact mul_ne_zero ht hs

theorem polynomialAncestorRows_normalized_isUnit_det {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0) :
    IsUnit ((polynomialAncestorRows steps).normalized φ).det := by
  induction steps with
  | nil =>
    simp [polynomialAncestorRows, PolynomialGiantRows.identity,
      PolynomialGiantRows.normalized, GiantRows.identity, GiantRows.det]
  | cons s steps ih =>
    have ht := ih (fun t ht => h t (by simp [ht]))
    have hs := h s (by simp)
    have hd := polynomialAncestorRows_denominator_ne_zero steps φ
      (fun t ht => (h t (by simp [ht])).2.2)
    change IsUnit (((polynomialAncestorRows steps).reverse s.left s.v s.w s.u).normalized φ).det
    rw [PolynomialGiantRows.normalized_reverse _ φ s.left s.v s.w s.u hd hs.1 hs.2.1 hs.2.2]
    exact GiantRows.isUnit_det_reverse _ ht _ _ _ _

/-- Every occurrence numerator formed after these actual reversals is nonzero
in the prime field. The current compensation variable is absent. -/
theorem polynomialAncestorRows_numeratorLine_nonzero {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0)
    (v w : MvPolynomial σ ℤ) (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    (((polynomialAncestorRows steps).numeratorLine v w).normalized φ).1 ≠ 0 ∨
      (((polynomialAncestorRows steps).numeratorLine v w).normalized φ).2 ≠ 0 := by
  have hd := polynomialAncestorRows_denominator_ne_zero steps φ (fun s hs => (h s hs).2.2)
  rw [PolynomialGiantRows.normalized_numeratorLine _ v w φ hd]
  have hdet := (polynomialAncestorRows_normalized_isUnit_det steps φ h).ne_zero
  simpa only [Units.val_mk0] using GiantRows.numerator_nonzero
    ((polynomialAncestorRows steps).normalized φ) hdet (Units.mk0 (φ v) hv) (Units.mk0 (φ w) hw)

end Ostmann

end OAI
