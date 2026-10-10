import OAI.NumberTheory.Ostmann.Arithmetic.MovingGiantRows
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticHistoryLines

namespace OAI

/-! # Cleared line bounds for the source-ordered moving giant histories -/

namespace Ostmann
namespace PolynomialGiantRows

variable {σ : Type*}

theorem denominator_movingReverse (T : PolynomialGiantRows σ) (left : Bool)
    (v w u : MvPolynomial σ ℤ) :
    (T.movingReverse left v w u).denominator = T.denominator * u := by
  cases left <;> rfl

theorem usesOnly_movingReverse [DecidableEq σ] (T : PolynomialGiantRows σ)
    (S : Finset σ) (hT : T.UsesOnly S) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) (hu : u.vars ⊆ S) :
    (T.movingReverse left v w u).UsesOnly S := by
  have h := usesOnly_reverse T S hT left v w u hv hw hu
  cases left
  · exact h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2⟩

theorem valueLE_movingReverse (T : PolynomialGiantRows σ)
    (φ : MvPolynomial σ ℤ →+* ℝ) (left : Bool) (v w u : MvPolynomial σ ℤ)
    (H L : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hT : T.ValueLE φ H)
    (hv : |φ v| ≤ L) (hw : |φ w| ≤ L) (hu : |φ u| ≤ L) :
    (T.movingReverse left v w u).ValueLE φ (2 * L * H) := by
  have h := valueLE_reverse T φ left v w u H L hH hL hT hv hw hu
  cases left
  · exact h
  · exact ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2⟩

end PolynomialGiantRows

noncomputable def movingPolynomialAncestors {σ : Type*} :
    List (PolynomialReversal σ) → PolynomialGiantRows σ
  | [] => PolynomialGiantRows.identity
  | s :: steps => (movingPolynomialAncestors steps).movingReverse s.left s.v s.w s.u

theorem movingPolynomialAncestors_denominator {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.u ≠ 0) :
    φ (movingPolynomialAncestors steps).denominator ≠ 0 := by
  induction steps with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity]
  | cons s steps ih =>
    rw [movingPolynomialAncestors, PolynomialGiantRows.denominator_movingReverse, map_mul]
    exact mul_ne_zero (ih fun t ht => h t (by simp [ht])) (h s (by simp))

theorem movingPolynomialAncestors_det {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0) :
    IsUnit ((movingPolynomialAncestors steps).normalized φ).det := by
  induction steps with
  | nil => simp [movingPolynomialAncestors, PolynomialGiantRows.identity,
      PolynomialGiantRows.normalized, GiantRows.identity, GiantRows.det]
  | cons s steps ih =>
    have hs := h s (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    have hd := movingPolynomialAncestors_denominator steps φ
      (fun t ht => (h t (by simp [ht])).2.2)
    rw [movingPolynomialAncestors, PolynomialGiantRows.normalized_movingReverse _ φ
      s.left s.v s.w s.u hd hs.1 hs.2.1 hs.2.2]
    exact GiantRows.isUnit_det_movingReverse _ ht _ _ _ _

theorem movingPolynomialAncestors_degree {σ : Type*}
    (steps : List (PolynomialReversal σ)) (d : ℕ)
    (h : ∀ s ∈ steps, s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d) :
    (movingPolynomialAncestors steps).DegreeLE (steps.length * d) := by
  induction steps with
  | nil => simpa only [movingPolynomialAncestors, List.length_nil, Nat.zero_mul] using
      (PolynomialGiantRows.degreeLE_identity (σ := σ))
  | cons s steps ih =>
    have hs := h s (by simp)
    simpa only [movingPolynomialAncestors, List.length_cons, Nat.add_mul, one_mul] using
      PolynomialGiantRows.degreeLE_movingReverse (movingPolynomialAncestors steps)
        s.left s.v s.w s.u (steps.length * d) d (ih fun t ht => h t (by simp [ht]))
        hs.1 hs.2.1 hs.2.2

theorem movingPolynomialAncestors_usesOnly {σ : Type*} [DecidableEq σ]
    (steps : List (PolynomialReversal σ)) (S : Finset σ)
    (h : ∀ s ∈ steps, s.v.vars ⊆ S ∧ s.w.vars ⊆ S ∧ s.u.vars ⊆ S) :
    (movingPolynomialAncestors steps).UsesOnly S := by
  induction steps with
  | nil => exact PolynomialGiantRows.usesOnly_identity S
  | cons s steps ih =>
    have hs := h s (by simp)
    exact PolynomialGiantRows.usesOnly_movingReverse _ S
      (ih fun t ht => h t (by simp [ht])) s.left s.v s.w s.u hs.1 hs.2.1 hs.2.2

theorem movingPolynomialAncestors_value {σ : Type*}
    (steps : List (PolynomialReversal σ)) (φ : MvPolynomial σ ℤ →+* ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ s ∈ steps, |φ s.v| ≤ L ∧ |φ s.w| ≤ L ∧ |φ s.u| ≤ L) :
    (movingPolynomialAncestors steps).ValueLE φ ((2 * L) ^ steps.length) := by
  induction steps with
  | nil => exact PolynomialGiantRows.valueLE_identity φ
  | cons s steps ih =>
    have hs := h s (by simp)
    have he : 2 * L * (2 * L) ^ steps.length = (2 * L) ^ (s :: steps).length := by
      rw [List.length_cons, pow_succ]
      ring
    rw [← he]
    exact PolynomialGiantRows.valueLE_movingReverse _ φ s.left s.v s.w s.u _ L
      (pow_nonneg (by positivity) _) hL (ih fun t ht => h t (by simp [ht]))
      hs.1 hs.2.1 hs.2.2

noncomputable def movingHistoryLine {σ : Type*} (steps : List (PolynomialReversal σ))
    (v w : MvPolynomial σ ℤ) : PolynomialGiantLine σ :=
  (movingPolynomialAncestors steps).numeratorLine v w

/-- Nonvanishing needed before the current compensation prime is sampled. -/
theorem movingHistoryLine_nonzero {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* K)
    (h : ∀ s ∈ steps, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0)
    (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    φ (movingHistoryLine steps v w).a ≠ 0 ∨ φ (movingHistoryLine steps v w).b ≠ 0 := by
  have hd := movingPolynomialAncestors_denominator steps φ (fun s hs => (h s hs).2.2)
  have hdet := (movingPolynomialAncestors_det steps φ h).ne_zero
  have hn := GiantRows.numerator_nonzero ((movingPolynomialAncestors steps).normalized φ)
    hdet (Units.mk0 (φ v) hv) (Units.mk0 (φ w) hw)
  have hn' : ((movingHistoryLine steps v w).normalized φ).1 ≠ 0 ∨
      ((movingHistoryLine steps v w).normalized φ).2 ≠ 0 := by
    rw [movingHistoryLine, PolynomialGiantRows.normalized_numeratorLine _ v w φ hd]
    simpa only [Units.val_mk0] using hn
  have hz := (movingHistoryLine steps v w).normalized_zero_iff φ hd
  exact hn'.imp (fun h h₀ => h (hz.1.mpr h₀)) (fun h h₀ => h (hz.2.mpr h₀))

/-- Concrete degree bound for the coefficient tests in the ancestor ordering. -/
theorem movingHistoryLine_degree {σ : Type*}
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (d : ℕ) (hs : ∀ s ∈ steps,
      s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d)
    (hv : v.totalDegree ≤ d) (hw : w.totalDegree ≤ d) :
    (movingHistoryLine steps v w).a.totalDegree ≤ (steps.length + 1) * d ∧
      (movingHistoryLine steps v w).b.totalDegree ≤ (steps.length + 1) * d := by
  simpa only [movingHistoryLine, Nat.add_mul, one_mul] using
    PolynomialGiantRows.numeratorLine_degree_le (movingPolynomialAncestors steps) v w
      (steps.length * d) d (movingPolynomialAncestors_degree steps d hs) hv hw

theorem movingHistoryLine_value {σ : Type*}
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hs : ∀ s ∈ steps, |φ s.v| ≤ L ∧ |φ s.w| ≤ L ∧ |φ s.u| ≤ L)
    (hv : |φ v| ≤ L) (hw : |φ w| ≤ L) :
    |φ (movingHistoryLine steps v w).a| ≤ (2 * L) ^ (steps.length + 1) ∧
      |φ (movingHistoryLine steps v w).b| ≤ (2 * L) ^ (steps.length + 1) := by
  have h := PolynomialGiantRows.numeratorLine_value_le (movingPolynomialAncestors steps)
    v w φ ((2 * L) ^ steps.length) L hL (movingPolynomialAncestors_value steps φ L hL hs) hv hw
  have he : 2 * L * (2 * L) ^ steps.length = (2 * L) ^ (steps.length + 1) := by
    rw [pow_succ]
    ring
  simpa only [movingHistoryLine, he] using h

theorem movingHistoryLine_vars_subset {σ : Type*} [DecidableEq σ]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ) (S : Finset σ)
    (hs : ∀ s ∈ steps, s.v.vars ⊆ S ∧ s.w.vars ⊆ S ∧ s.u.vars ⊆ S)
    (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) :
    (movingHistoryLine steps v w).a.vars ⊆ S ∧ (movingHistoryLine steps v w).b.vars ⊆ S :=
  PolynomialGiantRows.numeratorLine_vars_subset _ v w S
    (movingPolynomialAncestors_usesOnly steps S hs) hv hw

end Ostmann

end OAI
