import OAI.NumberTheory.Ostmann.Characters.PolynomialLineBounds
import OAI.NumberTheory.Ostmann.Characters.PolynomialAncestorNonvanishing

namespace OAI

/-! # The line tests produced by concrete ancestor histories -/

namespace Ostmann

noncomputable def historyLine {σ : Type*} (steps : List (PolynomialReversal σ))
    (v w : MvPolynomial σ ℤ) : PolynomialGiantLine σ :=
  (polynomialAncestorRows steps).numeratorLine v w

theorem historyLine_degree {σ : Type*} (steps : List (PolynomialReversal σ))
    (v w : MvPolynomial σ ℤ) (k d : ℕ) (hlen : steps.length ≤ k)
    (hs : ∀ s ∈ steps, s.v.totalDegree ≤ d ∧ s.w.totalDegree ≤ d ∧ s.u.totalDegree ≤ d)
    (hv : v.totalDegree ≤ d) (hw : w.totalDegree ≤ d) :
    (historyLine steps v w).a.totalDegree ≤ (k + 1) * d ∧
      (historyLine steps v w).b.totalDegree ≤ (k + 1) * d := by
  have h := PolynomialGiantRows.numeratorLine_degree_le (polynomialAncestorRows steps)
    v w (steps.length * d) d (polynomialAncestorRows_degree steps d hs) hv hw
  have hn : steps.length * d + d ≤ (k + 1) * d := by nlinarith
  exact ⟨h.1.trans hn, h.2.trans hn⟩

theorem historyLine_value {σ : Type*} (steps : List (PolynomialReversal σ))
    (v w : MvPolynomial σ ℤ) (φ : MvPolynomial σ ℤ →+* ℝ)
    (k : ℕ) (U : ℝ) (hU : 1 ≤ U) (hlen : steps.length ≤ k)
    (hs : ∀ s ∈ steps, |φ s.v| ≤ U ∧ |φ s.w| ≤ U ∧ |φ s.u| ≤ U)
    (hv : |φ v| ≤ U) (hw : |φ w| ≤ U) :
    |φ (historyLine steps v w).a| ≤ (2 * U) ^ (k + 1) ∧
      |φ (historyLine steps v w).b| ≤ (2 * U) ^ (k + 1) := by
  have hU0 : 0 ≤ U := by linarith
  have h := PolynomialGiantRows.numeratorLine_value_le (polynomialAncestorRows steps)
    v w φ ((2 * U) ^ steps.length) U hU0 (polynomialAncestorRows_value steps φ U hU0 hs) hv hw
  have hp : 2 * U * (2 * U) ^ steps.length ≤ (2 * U) ^ (k + 1) := by
    calc
      _ = (2 * U) ^ (steps.length + 1) := by rw [pow_succ]; ring
      _ ≤ _ := by gcongr; linarith
  exact ⟨h.1.trans hp, h.2.trans hp⟩

theorem historyLine_vars_subset {σ : Type*} [DecidableEq σ]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ) (S : Finset σ)
    (hs : ∀ s ∈ steps, s.v.vars ⊆ S ∧ s.w.vars ⊆ S ∧ s.u.vars ⊆ S)
    (hv : v.vars ⊆ S) (hw : w.vars ⊆ S) :
    (historyLine steps v w).a.vars ⊆ S ∧ (historyLine steps v w).b.vars ⊆ S :=
  PolynomialGiantRows.numeratorLine_vars_subset _ v w S
    (polynomialAncestorRows_usesOnly steps S hs) hv hw

theorem historyLine_denominator_ne_zero {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* K) (hs : ∀ s ∈ steps, φ s.u ≠ 0) :
    φ (historyLine steps v w).denominator ≠ 0 :=
  polynomialAncestorRows_denominator_ne_zero steps φ hs

theorem historyLine_nonzero {σ K : Type*} [Field K]
    (steps : List (PolynomialReversal σ)) (v w : MvPolynomial σ ℤ)
    (φ : MvPolynomial σ ℤ →+* K)
    (hs : ∀ s ∈ steps, φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0)
    (hv : φ v ≠ 0) (hw : φ w ≠ 0) :
    φ (historyLine steps v w).a ≠ 0 ∨ φ (historyLine steps v w).b ≠ 0 := by
  have hn := polynomialAncestorRows_numeratorLine_nonzero steps φ hs v w hv hw
  have hd := historyLine_denominator_ne_zero steps v w φ (fun s hs' => (hs s hs').2.2)
  have hz := (historyLine steps v w).normalized_zero_iff φ hd
  exact hn.imp (fun h h₀ => h (hz.1.mpr h₀)) (fun h h₀ => h (hz.2.mpr h₀))

end Ostmann

end OAI
