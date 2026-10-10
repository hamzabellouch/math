import OAI.NumberTheory.Ostmann.Characters.PolynomialWeightPair

namespace OAI

/-! # The actual argument-range cutoffs as polynomial inequalities -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def polynomialRangeBounds {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    Fin (n + n) → Polynomial ℝ :=
  Fin.append (fun i => (F i).polynomial - Polynomial.C (F i).lo)
    (fun i => Polynomial.C (F i).hi - (F i).polynomial)

noncomputable def polynomialRangeKeep (n : ℕ) (code : Fin (n + n) → Bool) : Bool :=
  decide (∀ i : Fin n, code (Fin.castAdd n i) = true ∧ code (Fin.natAdd n i) = true)

theorem polynomialRangeKeep_iff {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (x : ℝ) :
    polynomialRangeKeep n (polynomialSupportCode (polynomialRangeBounds F) x) = true ↔
      ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi := by
  simp only [polynomialRangeKeep, decide_eq_true_eq, polynomialSupportCode,
    polynomialRangeBounds, Fin.append_left, Fin.append_right,
    Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg, Set.mem_Icc]

/-- The clipped extension agrees exactly with the original smooth factors
multiplied by their sharp argument-range indicator. -/
theorem polynomialAmplitude_range {n : ℕ} (F : Fin n → ClippedPolynomialFactor) (x : ℝ) :
    polynomialAmplitude F (polynomialRangeBounds F) (polynomialRangeKeep n) x =
      (if ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi then (1 : ℂ) else 0) *
        ∏ i, (F i).profile ((F i).polynomial.eval x) := by
  unfold polynomialAmplitude
  by_cases h : ∀ i, (F i).polynomial.eval x ∈ Set.Icc (F i).lo (F i).hi
  · rw [ite_eq_left ((polynomialRangeKeep_iff F x).mpr h), ite_eq_left h]
    simp only [one_mul, smoothPolynomialWeight]
    exact Finset.prod_congr rfl (fun i _ => (F i).value_of_mem x (h i))
  · rw [ite_eq_right (fun hh => h ((polynomialRangeKeep_iff F x).mp hh)), ite_eq_right h]
    simp only [zero_mul]

theorem polynomialRangeBounds_degree_sum {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    (∑ i, (polynomialRangeBounds F i).natDegree) ≤
      2 * ∑ i, (F i).polynomial.natDegree := by
  simp only [polynomialRangeBounds, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hl : (∑ i, ((F i).polynomial - Polynomial.C (F i).lo).natDegree) ≤
      ∑ i, (F i).polynomial.natDegree := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)] using
      Polynomial.natDegree_sub_le (F i).polynomial (Polynomial.C (F i).lo)
  have hu : (∑ i, (Polynomial.C (F i).hi - (F i).polynomial).natDegree) ≤
      ∑ i, (F i).polynomial.natDegree := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)] using
      Polynomial.natDegree_sub_le (Polynomial.C (F i).hi) (F i).polynomial
  omega

theorem polynomialRange_complexity {n : ℕ} (F : Fin n → ClippedPolynomialFactor) :
    polynomialWeightComplexity F (polynomialRangeBounds F) ≤
      3 * ∑ i, (F i).polynomial.natDegree := by
  have hd : (∑ i, (F i).polynomial.derivative.natDegree) ≤
      ∑ i, (F i).polynomial.natDegree := by
    apply Finset.sum_le_sum
    intro i _
    exact (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hr := polynomialRangeBounds_degree_sum F
  unfold polynomialWeightComplexity
  omega

end Ostmann

end OAI
