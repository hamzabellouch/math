import OAI.NumberTheory.Ostmann.Construction.ExpandedWordPairBound
import OAI.NumberTheory.Ostmann.Construction.FormulaCoprimality

namespace OAI

/-! # History formulas on the original independent prime variables

Internal pivot addresses are initialized to one. Substitution removes them
from the polynomial variable type before the prime-divisibility estimate. -/

namespace Ostmann

open scoped Classical

namespace HistoryFormula

def originalPrimes {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) : HistoryFormula V :=
  F.bind (Sum.elim prime (fun _ => external 1))

theorem originalPrimes_value {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) (x : V → ℤ) :
    F.originalPrimes.value (fun i => (x i : ℚ)) =
      F.value (fun i => (expandedPrimeValues n x i : ℚ)) := by
  rw [originalPrimes, value_bind]
  congr 1
  funext i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, value_prime,
    value_external, expandedPrimeValues, Int.cast_one]

theorem originalPrimes_cost {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) :
    F.originalPrimes.cost = F.cost := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ (· + ·) ihf ihg
  | solve f g v w s hs ihf ihg =>
    change f.originalPrimes.cost + g.originalPrimes.cost + 2 = f.cost + g.cost + 2
    rw [ihf, ihg]

theorem originalPrimes_frequencies {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) :
    F.originalPrimes.frequencies = F.frequencies := by
  induction F with
  | prime i => cases i <;> rfl
  | external z => rfl
  | product f g ihf ihg => exact congrArg₂ List.append ihf ihg
  | solve f g v w s hs ihf ihg => exact congrArg (s :: ·) (congrArg₂ List.append ihf ihg)

theorem originalPrimes_denominator {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) :
    F.originalPrimes.cleared.denominator = F.cleared.denominator := by
  rw [denominator_eq_frequency_product, originalPrimes_frequencies,
    denominator_eq_frequency_product]

theorem originalPrimes_inputs {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) (R : ℝ) (hR : 1 ≤ R)
    (hF : F.InputsBounded R) : F.originalPrimes.InputsBounded R := by
  apply inputsBounded_bind F _ R hF
  intro i
  cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, InputsBounded, Int.cast_one, abs_one]
  exact hR

/-- The actual reconstructed integer and its collapsed polynomial have exactly
the same numerator, up to their common small-frequency denominator. -/
theorem originalPrimes_integer_value {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) (x : V → ℤ) (y : ℤ)
    (hy : F.value (fun i => (expandedPrimeValues n x i : ℚ)) = y) :
    MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.originalPrimes.cleared.numerator =
      F.cleared.denominator * y := by
  rw [← originalPrimes_denominator]
  apply ClearedHistoryValue.integer_value_cleared
  exact (F.originalPrimes_value x).trans hy

theorem originalPrimes_coprime {V : Type*} {n : ℕ}
    (F : HistoryFormula (ExpandedScheduledVariable V n)) (x : V → ℤ)
    (p : ℕ) (hp : p.Prime) (hd : ¬p ∣ F.cleared.denominator.natAbs) (y : ℤ)
    (hy : F.value (fun i => (expandedPrimeValues n x i : ℚ)) = y) :
    p.Coprime y.natAbs ↔ ¬p ∣
      (MvPolynomial.eval₂Hom (RingHom.id ℤ) x F.originalPrimes.cleared.numerator).natAbs := by
  rw [hp.coprime_iff_not_dvd,
    prime_dvd_cleared_iff p hp _ _ y (F.originalPrimes_integer_value x y hy) hd]

end HistoryFormula

end Ostmann

end OAI
