import Mathlib.Analysis.SpecialFunctions.Log.Basic
import OAI.NumberTheory.Ostmann.Characters.PolynomialGiantRows

namespace OAI

/-! # Size of the cleared arithmetic tests at actual prime values

A uniform bound on the slot values gives an explicit bound on every cleared
coefficient and denominator. This avoids any assumed bound on the height of
newly constructed polynomials.
-/

namespace Ostmann

namespace PolynomialGiantRows

variable {σ : Type*}

def ValueLE (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* ℝ) (H : ℝ) : Prop :=
  |φ T.rows.a| ≤ H ∧ |φ T.rows.b| ≤ H ∧ |φ T.rows.c| ≤ H ∧
    |φ T.rows.d| ≤ H ∧ |φ T.denominator| ≤ H

theorem valueLE_identity (φ : MvPolynomial σ ℤ →+* ℝ) :
    (identity : PolynomialGiantRows σ).ValueLE φ 1 := by
  simp [ValueLE, identity, GiantRows.identity]

theorem valueLE_reverse (T : PolynomialGiantRows σ) (φ : MvPolynomial σ ℤ →+* ℝ)
    (left : Bool) (v w u : MvPolynomial σ ℤ) (H L : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hT : T.ValueLE φ H)
    (hv : |φ v| ≤ L) (hw : |φ w| ≤ L) (hu : |φ u| ≤ L) :
    (T.reverse left v w u).ValueLE φ (2 * L * H) := by
  obtain ⟨ha, hb, hc, hd, hden⟩ := hT
  have hm (f g : MvPolynomial σ ℤ) (hf : |φ f| ≤ L) (hg : |φ g| ≤ H) :
      |φ (f * g)| ≤ L * H := by
    rw [map_mul, abs_mul]
    exact mul_le_mul hf hg (abs_nonneg _) hL
  have hs (f g : MvPolynomial σ ℤ) (hf : |φ f| ≤ L * H) (hg : |φ g| ≤ L * H) :
      |φ (f - g)| ≤ 2 * L * H := by
    rw [map_sub]
    exact (abs_sub _ _).trans (by linarith)
  have htwice : L * H ≤ 2 * L * H := by nlinarith
  have hden' : |φ (T.denominator * u)| ≤ 2 * L * H := by
    rw [mul_comm T.denominator u]
    exact (hm u T.denominator hu hden).trans htwice
  cases left <;> simp only [reverse, Bool.false_eq_true, ite_false, ite_true, ValueLE]
  · exact ⟨hs _ _ (hm v T.rows.c hv hc) (hm w T.rows.a hw ha),
      hs _ _ (hm v T.rows.d hv hd) (hm w T.rows.b hw hb),
      (hm _ _ hu hc).trans htwice, (hm _ _ hu hd).trans htwice, hden'⟩
  · exact ⟨(hm _ _ hu ha).trans htwice, (hm _ _ hu hb).trans htwice,
      hs _ _ (hm v T.rows.c hv hc) (hm w T.rows.a hw ha),
      hs _ _ (hm v T.rows.d hv hd) (hm w T.rows.b hw hb), hden'⟩

/-- A minor of two bounded coefficient rows has the stated elementary size. -/
theorem minor_value_le (φ : MvPolynomial σ ℤ →+* ℝ) (a b c d : MvPolynomial σ ℤ)
    (H : ℝ) (hH : 0 ≤ H) (ha : |φ a| ≤ H) (hb : |φ b| ≤ H)
    (hc : |φ c| ≤ H) (hd : |φ d| ≤ H) : |φ (a * d - b * c)| ≤ 2 * H ^ 2 := by
  have h₁ : |φ a * φ d| ≤ H * H := by
    rw [abs_mul]
    exact mul_le_mul ha hd (abs_nonneg _) hH
  have h₂ : |φ b * φ c| ≤ H * H := by
    rw [abs_mul]
    exact mul_le_mul hb hc (abs_nonneg _) hH
  simp only [map_sub, map_mul]
  exact (abs_sub _ _).trans (by nlinarith)

end PolynomialGiantRows

theorem polynomialAncestorRows_value {σ : Type*} (steps : List (PolynomialReversal σ))
    (φ : MvPolynomial σ ℤ →+* ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ s ∈ steps, |φ s.v| ≤ L ∧ |φ s.w| ≤ L ∧ |φ s.u| ≤ L) :
    (polynomialAncestorRows steps).ValueLE φ ((2 * L) ^ steps.length) := by
  induction steps with
  | nil => simpa only [polynomialAncestorRows, List.length_nil, pow_zero] using
      PolynomialGiantRows.valueLE_identity φ
  | cons s steps ih =>
    have hs := h s (by simp)
    have ht := ih (fun t ht => h t (by simp [ht]))
    have he : 2 * L * (2 * L) ^ steps.length = (2 * L) ^ (s :: steps).length := by
      rw [List.length_cons, pow_succ]
      ring
    rw [← he]
    exact PolynomialGiantRows.valueLE_reverse _ φ s.left s.v s.w s.u _ L
      (pow_nonneg (by positivity) _) hL ht hs.1 hs.2.1 hs.2.2

/-- Convert the concrete multiplicative size bound to the logarithmic budget
used when counting accidental prime divisors. -/
theorem log_abs_le_of_power_bound (x H : ℝ) (n : ℕ) (hx : x ≠ 0)
    (hbound : |x| ≤ H ^ n) : Real.log |x| ≤ (n : ℝ) * Real.log H := by
  have h := Real.log_le_log (abs_pos.mpr hx) hbound
  rwa [Real.log_pow] at h

end Ostmann

end OAI
