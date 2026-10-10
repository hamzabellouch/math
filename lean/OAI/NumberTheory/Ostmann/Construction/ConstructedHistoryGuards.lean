import OAI.NumberTheory.Ostmann.Arithmetic.IndexedHistoryReconstruction
import OAI.NumberTheory.Ostmann.Construction.FullHistoryGuards

namespace OAI

/-! # Exact range and residue guards for the reconstructed original pivots -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def formulaPolynomial {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℝ) (coord : σ) : Polynomial ℝ :=
  normalizedHistoryPolynomial F.cleared.numerator a coord F.cleared.denominator

theorem formulaPolynomial_degree {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℝ) (coord : σ) : (formulaPolynomial F a coord).natDegree ≤ F.cost :=
  (normalizedHistoryPolynomial_natDegree _ _ _ _).trans F.degree_le_cost

noncomputable def formulaRangePolynomials {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ) (lo hi : Fin n → ℝ) :
    Fin (n + n) → Polynomial ℝ :=
  Fin.append (fun i => formulaPolynomial (F i) a coord - Polynomial.C (lo i))
    (fun i => Polynomial.C (hi i) - formulaPolynomial (F i) a coord)

theorem formulaRangePolynomials_iff {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ) (lo hi : Fin n → ℝ) (x : ℝ) :
    polynomialRangeKeep n (polynomialSupportCode (formulaRangePolynomials F a coord lo hi) x) = true ↔
      ∀ i, (formulaPolynomial (F i) a coord).eval x ∈ Set.Icc (lo i) (hi i) := by
  simp only [polynomialRangeKeep, decide_eq_true_eq, polynomialSupportCode,
    formulaRangePolynomials, Fin.append_left, Fin.append_right,
    Polynomial.eval_sub, Polynomial.eval_C, sub_nonneg, Set.mem_Icc]

theorem formulaRangePolynomials_degree {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ) (lo hi : Fin n → ℝ) :
    (∑ i, (formulaRangePolynomials F a coord lo hi i).natDegree) ≤ 2 * ∑ i, (F i).cost := by
  simp only [formulaRangePolynomials, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hl : (∑ i, (formulaPolynomial (F i) a coord - Polynomial.C (lo i)).natDegree) ≤
      ∑ i, (F i).cost := by
    apply Finset.sum_le_sum
    intro i _
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
    exact formulaPolynomial_degree _ _ _
  have hu : (∑ i, (Polynomial.C (hi i) - formulaPolynomial (F i) a coord).natDegree) ≤
      ∑ i, (F i).cost := by
    apply Finset.sum_le_sum
    intro i _
    apply (Polynomial.natDegree_sub_le _ _).trans
    simp only [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)]
    exact formulaPolynomial_degree _ _ _
  omega

theorem formulaPolynomial_integer_value {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℤ) (coord : σ) (z y : ℤ)
    (hy : F.value (fun j => (Function.update a coord z j : ℚ)) = y) :
    (formulaPolynomial F (fun j => (a j : ℝ)) coord).eval (z : ℝ) = (y : ℝ) := by
  rw [formulaPolynomial, normalizedHistoryPolynomial_eval]
  have hupdate : Function.update (fun j => (a j : ℝ)) coord (z : ℝ) =
      fun j => (Function.update a coord z j : ℝ) := by
    funext j
    by_cases hj : j = coord
    · subst j; simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  rw [hupdate]
  exact F.cleared.real_value_of_integer _ y hy

theorem reconstructedPivot_ranges {σ : Type*} (steps : List (HistoryPivotStep σ))
    (a : σ → ℤ) (coord : σ) (lo hi : Fin steps.length → ℝ) (z : ℤ)
    (hz : ValidIntegerReconstruction steps (Function.update a coord z)) :
    polynomialRangeKeep steps.length (polynomialSupportCode
      (formulaRangePolynomials (reconstructionFormulaAt steps .prime)
        (fun j => (a j : ℝ)) coord lo hi) z) = true ↔
      ∀ i, (reconstructedPivotAt steps (Function.update a coord z) i : ℝ) ∈ Set.Icc (lo i) (hi i) := by
  rw [formulaRangePolynomials_iff]
  apply forall_congr'
  intro i
  rw [formulaPolynomial_integer_value _ a coord z _
    (reconstructionFormulaAt_value steps .prime _ _
      (fun j => HistoryFormula.value_prime j _) hz i)]

noncomputable def reconstructedHistoryAmplitude {σ : Type*} {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (s : Fin steps.length → ℕ)
    (a : σ → ℤ) (coord : σ) (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (z : ℤ) : ℂ :=
  (if ValidIntegerReconstruction steps (Function.update a coord z) ∧
      ∀ i, IsUnit ((reconstructedPivotAt steps (Function.update a coord z) i : ℤ) : ZMod (s i))
    then 1 else 0) * polynomialAmplitude F H keep z

theorem reconstructedHistoryAmplitude_exact {σ : Type*} {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (s : Fin steps.length → ℕ)
    (a : σ → ℤ) (coord : σ) (F : Fin n → ClippedPolynomialFactor)
    (H : Fin t → Polynomial ℝ) (keep : (Fin t → Bool) → Bool) (z : ℤ) :
    reconstructedHistoryAmplitude steps s a coord F H keep z =
      guardedHistoryAmplitude
        (fun i => (reconstructionFormulaAt steps .prime i).cleared.numerator)
        (fun i => (reconstructionFormulaAt steps .prime i).cleared.denominator)
        s a coord F H keep z := by
  have ht := reconstruction_small_tests_iff steps (Function.update a coord z) s
  simp only [MvPolynomial.coe_eval₂Hom] at ht
  simp only [reconstructedHistoryAmplitude, guardedHistoryAmplitude, ht]

end Ostmann

end OAI
