import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticIntegerComparison
import OAI.NumberTheory.Ostmann.Arithmetic.InternalLineProbability

namespace OAI

/-! # The exact cleared polynomial flags for an internal line system -/

namespace Ostmann

noncomputable section

open scoped Classical

/-- The distinguished row supplies the coefficient tests; its minors with
all other rows supply the rank tests. -/
def lineTestPolynomials {σ J : Type*} (L : J → PolynomialGiantLine σ) (i : J) :
    Bool ⊕ J → MvPolynomial σ ℤ
  | .inl false => (L i).a
  | .inl true => (L i).b
  | .inr j => (L i).minor (L j)

def lineFeasibleFlags {J : Type*} (external : Bool) (f : Bool ⊕ J → Bool) : Prop :=
  f (.inl false) = false ∧ (external = true ∨ f (.inl true) = false) ∧
    ∀ j, f (.inr j) = true

theorem external_polynomialLine_flags_iff {σ J K : Type*} [Field K]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* K)
    (hd : ∀ j, φ (L j).denominator ≠ 0) :
    lineFeasibleFlags true (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) ↔
      externalLineFeasible (fun j => ((L j).normalized φ).1)
        (fun j => ((L j).normalized φ).2) i := by
  simp only [lineFeasibleFlags, lineTestPolynomials, arithmeticTestFlag_eq_false_iff,
    arithmeticTestFlag_eq_true_iff, true_or, true_and, externalLineFeasible, lineRankOne]
  apply and_congr
  · exact (not_congr ((L i).normalized_zero_iff φ (hd i)).1).symm
  · exact forall_congr' fun j =>
      ((L i).normalized_minor_zero_iff (L j) φ (hd i) (hd j)).symm

theorem unit_polynomialLine_flags_iff {σ J K : Type*} [Field K]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* K)
    (hd : ∀ j, φ (L j).denominator ≠ 0) :
    lineFeasibleFlags false (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) ↔
      unitLineFeasible (fun j => ((L j).normalized φ).1)
        (fun j => ((L j).normalized φ).2) i := by
  simp only [lineFeasibleFlags, lineTestPolynomials, arithmeticTestFlag_eq_false_iff,
    arithmeticTestFlag_eq_true_iff, Bool.false_eq_true, false_or,
    unitLineFeasible, lineRankOne]
  apply and_congr
  · exact (not_congr ((L i).normalized_zero_iff φ (hd i)).1).symm
  · apply and_congr
    · exact (not_congr ((L i).normalized_zero_iff φ (hd i)).2).symm
    · exact forall_congr' fun j =>
        ((L i).normalized_minor_zero_iff (L j) φ (hd i) (hd j)).symm

/-- The divisibility flags of the actual integer evaluations agree exactly
with zero tests in the prime residue field. -/
theorem line_divisibility_flags_eq {J A : Type*} {n : ℕ} (value : A → ℤ)
    (L : J → PolynomialGiantLine (Fin n)) (i : J) (x : Fin n → A) (p : ℕ) :
    (fun s => arithmeticTestFlag (p ∣ (integerTestValue value (lineTestPolynomials L i s) x).natAbs)) =
      (fun s => arithmeticTestFlag
        (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p))
          (fun j => (value (x j) : ZMod p)) (lineTestPolynomials L i s) = 0)) := by
  funext s
  apply congrArg arithmeticTestFlag
  apply propext
  exact (Int.natCast_dvd).symm.trans
    (integerPolynomial_mod_zero_iff (fun j => value (x j)) _ p).symm

end

end Ostmann

end OAI
