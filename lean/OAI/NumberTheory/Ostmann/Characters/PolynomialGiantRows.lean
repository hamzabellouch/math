import Mathlib.Algebra.MvPolynomial.CommRing
import OAI.NumberTheory.Ostmann.Construction.GiantReversalRows

namespace OAI

/-! # Clearing denominators along the giant histories

The five integer polynomials below represent both coefficient rows with a
common denominator. Each reversal uses only multiplication and subtraction;
their degree grows by at most the degree of the new slot data.
-/

namespace Ostmann

noncomputable section

structure PolynomialGiantRows (σ : Type*) where
  rows : GiantRows (MvPolynomial σ ℤ)
  denominator : MvPolynomial σ ℤ

namespace PolynomialGiantRows

variable {σ : Type*}

def identity : PolynomialGiantRows σ := ⟨GiantRows.identity, 1⟩

def reverse (T : PolynomialGiantRows σ) (left : Bool) (v w u : MvPolynomial σ ℤ) :
    PolynomialGiantRows σ :=
  if left then
    ⟨⟨u * T.rows.a, u * T.rows.b, v * T.rows.c - w * T.rows.a,
      v * T.rows.d - w * T.rows.b⟩, T.denominator * u⟩
  else
    ⟨⟨v * T.rows.c - w * T.rows.a, v * T.rows.d - w * T.rows.b,
      u * T.rows.c, u * T.rows.d⟩, T.denominator * u⟩

/-- Normalized coefficients after evaluating all small prime variables. -/
def normalized {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) : GiantRows K :=
  ⟨φ T.rows.a / φ T.denominator, φ T.rows.b / φ T.denominator,
    φ T.rows.c / φ T.denominator, φ T.rows.d / φ T.denominator⟩

private theorem retained_quotient {K : Type*} [Field K] (a d u : K) (hu : u ≠ 0) :
    (u * a) / (d * u) = a / d := by
  field_simp

private theorem reversed_quotient {K : Type*} [Field K] (a c d v w u : K)
    (hd : d ≠ 0) (hu : u ≠ 0) :
    (v * c - w * a) / (d * u) = u⁻¹ * (v * (c / d) - w * (a / d)) := by
  field_simp

/-- The polynomial recurrence evaluates to the actual rational reversal. -/
theorem normalized_reverse {K : Type*} [Field K] (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* K) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hd : φ T.denominator ≠ 0) (hv : φ v ≠ 0) (hw : φ w ≠ 0) (hu : φ u ≠ 0) :
    (T.reverse left v w u).normalized φ =
      (T.normalized φ).reverse left (Units.mk0 (φ v) hv) (Units.mk0 (φ w) hw)
        (Units.mk0 (φ u) hu) := by
  cases left <;> apply GiantRows.ext <;>
    simp only [reverse, normalized, GiantRows.reverse, Bool.false_eq_true, ite_false,
      ite_true, map_mul, map_sub, Units.val_mk0, Units.val_inv_eq_inv_val]
  all_goals first
    | exact retained_quotient _ _ _ hu
    | exact reversed_quotient _ _ _ _ _ _ hd hu

/-- A simultaneous degree bound for the four cleared coefficients and denominator. -/
def DegreeLE (T : PolynomialGiantRows σ) (d : ℕ) : Prop :=
  T.rows.a.totalDegree ≤ d ∧ T.rows.b.totalDegree ≤ d ∧
    T.rows.c.totalDegree ≤ d ∧ T.rows.d.totalDegree ≤ d ∧ T.denominator.totalDegree ≤ d

theorem degreeLE_identity : (identity : PolynomialGiantRows σ).DegreeLE 0 := by
  simp [DegreeLE, identity, GiantRows.identity]

theorem degreeLE_reverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) (d e : ℕ) (hT : T.DegreeLE d)
    (hv : v.totalDegree ≤ e) (hw : w.totalDegree ≤ e) (hu : u.totalDegree ≤ e) :
    (T.reverse left v w u).DegreeLE (d + e) := by
  obtain ⟨ha, hb, hc, hd, hden⟩ := hT
  have hmul (f g : MvPolynomial σ ℤ) (hf : f.totalDegree ≤ e) (hg : g.totalDegree ≤ d) :
      (f * g).totalDegree ≤ d + e :=
    (MvPolynomial.totalDegree_mul f g).trans (by omega)
  have hsub (f g : MvPolynomial σ ℤ) (hf : f.totalDegree ≤ d + e)
      (hg : g.totalDegree ≤ d + e) : (f - g).totalDegree ≤ d + e :=
    (MvPolynomial.totalDegree_sub f g).trans (max_le hf hg)
  have hden' : (T.denominator * u).totalDegree ≤ d + e :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hden hu)
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, ite_true, DegreeLE]
  · exact ⟨hsub _ _ (hmul _ _ hv hc) (hmul _ _ hw ha),
      hsub _ _ (hmul _ _ hv hd) (hmul _ _ hw hb), hmul _ _ hu hc, hmul _ _ hu hd, hden'⟩
  · exact ⟨hmul _ _ hu ha, hmul _ _ hu hb,
      hsub _ _ (hmul _ _ hv hc) (hmul _ _ hw ha),
      hsub _ _ (hmul _ _ hv hd) (hmul _ _ hw hb), hden'⟩

end PolynomialGiantRows

structure PolynomialReversal (σ : Type*) where
  left : Bool
  v : MvPolynomial σ ℤ
  w : MvPolynomial σ ℤ
  u : MvPolynomial σ ℤ

def polynomialAncestorRows {σ : Type*} : List (PolynomialReversal σ) → PolynomialGiantRows σ
  | [] => PolynomialGiantRows.identity
  | s :: steps => (polynomialAncestorRows steps).reverse s.left s.v s.w s.u

theorem polynomialAncestorRows_degree {σ : Type*} (steps : List (PolynomialReversal σ))
    (d : ℕ) (h : ∀ s ∈ steps, s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d) :
    (polynomialAncestorRows steps).DegreeLE (steps.length * d) := by
  induction steps with
  | nil => simpa only [polynomialAncestorRows, List.length_nil, Nat.zero_mul] using
      (PolynomialGiantRows.degreeLE_identity (σ := σ))
  | cons s steps ih =>
    have hs := h s (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    simpa only [polynomialAncestorRows, List.length_cons, Nat.add_mul, one_mul] using
      PolynomialGiantRows.degreeLE_reverse (polynomialAncestorRows steps) s.left s.v s.w s.u
        (steps.length * d) d ht hs.1 hs.2.1 hs.2.2

end

end Ostmann

end OAI
