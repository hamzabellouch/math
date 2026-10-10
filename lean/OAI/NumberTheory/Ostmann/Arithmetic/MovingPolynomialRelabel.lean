import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotRelabel

namespace OAI

/-! # Polynomial transport when repeated prime labels are identified -/

namespace Ostmann
open scoped Classical

noncomputable def PolynomialGiantRows.rename {σ τ : Type*} (f : σ → τ)
    (T : PolynomialGiantRows σ) : PolynomialGiantRows τ :=
  ⟨⟨MvPolynomial.rename f T.rows.a, MvPolynomial.rename f T.rows.b,
    MvPolynomial.rename f T.rows.c, MvPolynomial.rename f T.rows.d⟩,
    MvPolynomial.rename f T.denominator⟩

noncomputable def PolynomialReversal.rename {σ τ : Type*} (f : σ → τ)
    (s : PolynomialReversal σ) : PolynomialReversal τ :=
  ⟨s.left, MvPolynomial.rename f s.v, MvPolynomial.rename f s.w, MvPolynomial.rename f s.u⟩

theorem PolynomialGiantRows.rename_movingReverse {σ τ : Type*} (f : σ → τ)
    (T : PolynomialGiantRows σ) (b : Bool) (v w u : MvPolynomial σ ℤ) :
    (T.movingReverse b v w u).rename f =
      (T.rename f).movingReverse b (MvPolynomial.rename f v)
        (MvPolynomial.rename f w) (MvPolynomial.rename f u) := by
  cases b <;> simp [rename, movingReverse, reverse, swap, GiantRows.swap]

theorem movingSlotCoefficient_rename {σ τ : Type*} (f : σ → τ)
    (s : ℤ) (slots : List σ) :
    MvPolynomial.rename f (movingSlotCoefficient s slots) =
      movingSlotCoefficient s (slots.map f) := by
  simp [movingSlotCoefficient, movingSlotProduct, map_list_prod, List.map_map, Function.comp_def]

theorem MovingSlotReversal.polynomial_map {σ τ : Type*} (f : σ → τ)
    (s : MovingSlotReversal σ) : (s.map f).polynomial = s.polynomial.rename f := by
  simp [polynomial, map, PolynomialReversal.rename, movingSlotCoefficient_rename]

theorem movingPolynomialAncestors_rename {σ τ : Type*} (f : σ → τ)
    (steps : List (PolynomialReversal σ)) :
    movingPolynomialAncestors (steps.map (PolynomialReversal.rename f)) =
      (movingPolynomialAncestors steps).rename f := by
  induction steps with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity,
      PolynomialGiantRows.rename, GiantRows.identity]
  | cons s steps ih =>
    simp only [List.map_cons, movingPolynomialAncestors, ih,
      PolynomialReversal.rename, PolynomialGiantRows.rename_movingReverse]

/-- In particular, identifying repeated labels preserves the cleared line
polynomials, including every ancestor denominator. -/
theorem movingSlotLine_map {σ τ : Type*} (f : σ → τ)
    (path : List (MovingSlotReversal σ)) (current : MovingSlotReversal σ) :
    let L := movingSlotLine path current
    let L' := movingSlotLine (path.map (MovingSlotReversal.map f)) (current.map f)
    L'.a = MvPolynomial.rename f L.a ∧
      L'.b = MvPolynomial.rename f L.b ∧
      L'.denominator = MvPolynomial.rename f L.denominator := by
  have hs : (path.map (MovingSlotReversal.map f)).map MovingSlotReversal.polynomial =
      (path.map MovingSlotReversal.polynomial).map (PolynomialReversal.rename f) := by
    simp only [List.map_map]
    congr 1
    funext s
    exact MovingSlotReversal.polynomial_map f s
  simp only [movingSlotLine, hs, movingPolynomialAncestors_rename, movingHistoryLine,
    MovingSlotReversal.polynomial_map, PolynomialReversal.rename]
  simp [PolynomialGiantRows.numeratorLine, PolynomialGiantRows.rename]

end Ostmann

end OAI
