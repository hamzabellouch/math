import OAI.NumberTheory.Ostmann.Construction.ConstructedHistoryGuards
import OAI.NumberTheory.Ostmann.Construction.HistoryFourierPolynomial

namespace OAI

/-! # Fourier factors of the constructed history formulas, with derived budgets -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

noncomputable def formulaFourierFactors {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) : Fin n → ClippedPolynomialFactor :=
  fun j => historyFourierFactor (F j).cleared.numerator a coord
    (F j).cleared.denominator (X j) ψ (v j) (lo j) (hi j) (hlo j) (hhi j)

noncomputable def formulaFourierBudget {n : ℕ} (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ) : ℝ :=
  ∏ j, (2 * SchwartzMap.seminorm ℝ 0 0 ψ +
    (SchwartzMap.seminorm ℝ 0 0 ψ + SchwartzMap.seminorm ℝ 0 1 ψ * |v j|) * (hi j - lo j))

theorem formulaFourierFactors_budget {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) :
    smoothPolynomialBudget (formulaFourierFactors F a coord X ψ v lo hi hlo hhi) =
      formulaFourierBudget ψ v lo hi := rfl

theorem formulaFourierBudget_nonneg {n : ℕ} (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hhi : ∀ j, lo j ≤ hi j) : 0 ≤ formulaFourierBudget ψ v lo hi := by
  have hψ : 0 ≤ SchwartzMap.seminorm ℝ 0 0 ψ :=
    (norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)
  exact Finset.prod_nonneg fun j _ => add_nonneg (mul_nonneg (by norm_num) hψ)
    (mul_nonneg (add_nonneg hψ (mul_nonneg (schwartz_profile_lip_nonneg ψ) (abs_nonneg _)))
      (sub_nonneg.mpr (hhi j)))

theorem formulaFourierFactors_degree {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℝ) (coord : σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (j : Fin n) :
    ((formulaFourierFactors F a coord X ψ v lo hi hlo hhi) j).polynomial.natDegree ≤
      (F j).cost :=
  (normalizedHistoryPolynomial_natDegree _ _ _ _).trans (F j).degree_le_cost

/-- All critical points, Fourier ranges, and original word/pivot ranges
have a polynomial complexity obtained from the actual formula costs. -/
theorem formulaFourier_full_complexity {σ : Type*} {n t : ℕ}
    (F : Fin n → HistoryFormula σ) (G : Fin t → HistoryFormula σ)
    (a : σ → ℝ) (coord : σ) (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ))
    (v lo hi : Fin n → ℝ) (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j)
    (glo ghi : Fin t → ℝ) :
    let factors := formulaFourierFactors F a coord X ψ v lo hi hlo hhi
    let ranges := formulaRangePolynomials G a coord glo ghi
    polynomialWeightComplexity factors (fullHistoryPolynomials factors ranges) ≤
      3 * (∑ j, (F j).cost) + 2 * ∑ j, (G j).cost := by
  apply (fullHistoryPolynomials_complexity _ _).trans
  apply Nat.add_le_add
  · apply Nat.mul_le_mul_left
    exact Finset.sum_le_sum fun j _ => formulaFourierFactors_degree F a coord X ψ v lo hi hlo hhi j
  · exact formulaRangePolynomials_degree G a coord glo ghi

theorem formulaFourierFactor_integer_value {σ : Type*}
    (F : HistoryFormula σ) (a : σ → ℤ) (coord : σ) (z M : ℤ)
    (hy : F.value (fun j => (Function.update a coord z j : ℚ)) = M)
    (X : ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hX : X ≠ 0) (hM : M ≠ 0) (hrange : (M : ℝ) / X ∈ Set.Icc lo hi) :
    (historyFourierFactor F.cleared.numerator (fun j => (a j : ℝ)) coord
      F.cleared.denominator X ψ v lo hi hlo hhi).value (z : ℝ) =
      archimedeanLeafFactor X M v 1 ψ := by
  apply fourierPolynomialFactor_original _ ψ v lo hi hlo hhi z X M hX
    (Int.cast_ne_zero.mpr hM)
  · rw [normalizedHistoryPolynomial_eval, ← div_div]
    have he := formulaPolynomial_integer_value F a coord z M hy
    rw [formulaPolynomial, normalizedHistoryPolynomial_eval] at he
    rw [he]
  · rw [normalizedHistoryPolynomial_eval, ← div_div]
    have he := formulaPolynomial_integer_value F a coord z M hy
    rw [formulaPolynomial, normalizedHistoryPolynomial_eval] at he
    rwa [he]

end Ostmann

end OAI
