import OAI.NumberTheory.Ostmann.Characters.PolynomialRangeGuards
import OAI.NumberTheory.Ostmann.Construction.HistoryPolynomialSpecialization

namespace OAI

/-! # Exact polynomial guards for ranges of reconstructed rational integers -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def clearedIntervalPolynomials (P : Polynomial ℝ) (d lo hi : ℝ) :
    Fin 2 → Polynomial ℝ :=
  ![Polynomial.C d * (P - Polynomial.C (lo * d)),
    Polynomial.C d * (Polynomial.C (hi * d) - P)]

def clearedIntervalKeep (code : Fin 2 → Bool) : Bool := code 0 && code 1

theorem cleared_interval_test (N d lo hi : ℝ) (hd : d ≠ 0) :
    (0 ≤ d * (N - lo * d) ∧ 0 ≤ d * (hi * d - N)) ↔ N / d ∈ Set.Icc lo hi := by
  have hsq : 0 < d ^ 2 := sq_pos_of_ne_zero hd
  have hl : d * (N - lo * d) = d ^ 2 * (N / d - lo) := by field_simp
  have hu : d * (hi * d - N) = d ^ 2 * (hi - N / d) := by field_simp
  rw [hl, hu, mul_nonneg_iff_of_pos_left hsq, mul_nonneg_iff_of_pos_left hsq]
  exact ⟨fun h => ⟨sub_nonneg.mp h.1, sub_nonneg.mp h.2⟩,
    fun h => ⟨sub_nonneg.mpr h.1, sub_nonneg.mpr h.2⟩⟩

theorem clearedIntervalKeep_iff (P : Polynomial ℝ) (d lo hi x : ℝ) (hd : d ≠ 0) :
    clearedIntervalKeep (polynomialSupportCode (clearedIntervalPolynomials P d lo hi) x) = true ↔
      P.eval x / d ∈ Set.Icc lo hi := by
  simp only [clearedIntervalKeep, Bool.and_eq_true, polynomialSupportCode,
    decide_eq_true_eq, clearedIntervalPolynomials, Matrix.cons_val_zero,
    Matrix.cons_val_one, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C]
  exact cleared_interval_test (P.eval x) d lo hi hd

theorem clearedIntervalPolynomials_degree (P : Polynomial ℝ) (d lo hi : ℝ) :
    (∑ j, (clearedIntervalPolynomials P d lo hi j).natDegree) ≤ 2 * P.natDegree := by
  have hleft : (Polynomial.C d * (P - Polynomial.C (lo * d))).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, zero_add, max_eq_left (Nat.zero_le _)] using
        Polynomial.natDegree_sub_le P (Polynomial.C (lo * d)))
  have hright : (Polynomial.C d * (Polynomial.C (hi * d) - P)).natDegree ≤ P.natDegree :=
    Polynomial.natDegree_mul_le.trans (by
      simpa only [Polynomial.natDegree_C, zero_add, max_eq_right (Nat.zero_le _)] using
        Polynomial.natDegree_sub_le (Polynomial.C (hi * d)) P)
  simp only [Fin.sum_univ_two, clearedIntervalPolynomials, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- Fixing the other primes gives the literal range test on the cleared
history numerator. Denominator signs require no separate cases. -/
theorem specialized_cleared_interval_test {σ : Type*} (P : MvPolynomial σ ℤ)
    (a : σ → ℝ) (i : σ) (d lo hi x : ℝ) (hd : d ≠ 0) :
    clearedIntervalKeep (polynomialSupportCode
      (clearedIntervalPolynomials (specializeHistoryVariable a i P) d lo hi) x) = true ↔
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Function.update a i x) P / d ∈ Set.Icc lo hi := by
  rw [clearedIntervalKeep_iff _ d lo hi x hd, specializeHistoryVariable_eval]

end Ostmann

end OAI
