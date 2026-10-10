import OAI.NumberTheory.Ostmann.Construction.HistoryFormulaFourier

namespace OAI

/-! # The global history coefficient and its exact one-variable polynomial form -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

noncomputable def HistoryFormula.realValue {σ : Type*} (F : HistoryFormula σ) (x : σ → ℤ) : ℝ :=
  MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => (x i : ℝ)) F.cleared.numerator /
    F.cleared.denominator

theorem formulaPolynomial_eval_update {σ : Type*} (F : HistoryFormula σ)
    (a : σ → ℤ) (coord : σ) (z : ℤ) :
    (formulaPolynomial F (fun j => (a j : ℝ)) coord).eval (z : ℝ) =
      F.realValue (Function.update a coord z) := by
  rw [formulaPolynomial, normalizedHistoryPolynomial_eval]
  unfold HistoryFormula.realValue
  congr 2
  funext j
  by_cases hj : j = coord
  · subst j; simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]

theorem formulaFourier_polynomial_eval {σ : Type*} {n : ℕ}
    (F : Fin n → HistoryFormula σ) (a : σ → ℤ) (coord : σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (j : Fin n) (z : ℤ) :
    ((formulaFourierFactors F (fun i => (a i : ℝ)) coord X ψ v lo hi hlo hhi) j).polynomial.eval (z : ℝ) =
      (F j).realValue (Function.update a coord z) / X j := by
  change (normalizedHistoryPolynomial _ _ _ ((F j).cleared.denominator * X j)).eval (z : ℝ) = _
  rw [normalizedHistoryPolynomial_eval, ← div_div]
  have he := formulaPolynomial_eval_update (F j) a coord z
  rw [formulaPolynomial, normalizedHistoryPolynomial_eval] at he
  rw [he]

noncomputable def globalHistoryArchCoefficient {σ : Type*} {n t : ℕ}
    (F : Fin n → HistoryFormula σ) (G : Fin t → HistoryFormula σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (glo ghi : Fin t → ℝ) (x : σ → ℤ) : ℂ :=
  (if (∀ j, (G j).realValue x ∈ Set.Icc (glo j) (ghi j)) ∧
      (∀ j, (F j).realValue x / X j ∈ Set.Icc (lo j) (hi j)) then 1 else 0) *
    ∏ j, normalizedFourierProfile ψ (v j) ((F j).realValue x / X j)

theorem globalHistoryArchCoefficient_local {σ : Type*} {n t : ℕ}
    (F : Fin n → HistoryFormula σ) (G : Fin t → HistoryFormula σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (glo ghi : Fin t → ℝ)
    (a : σ → ℤ) (coord : σ) (z : ℤ) :
    globalHistoryArchCoefficient F G X ψ v lo hi glo ghi (Function.update a coord z) =
      polynomialAmplitude (formulaFourierFactors F (fun j => (a j : ℝ)) coord X ψ v lo hi hlo hhi)
        (fullHistoryPolynomials (formulaFourierFactors F (fun j => (a j : ℝ)) coord X ψ v lo hi hlo hhi)
          (formulaRangePolynomials G (fun j => (a j : ℝ)) coord glo ghi))
        (fullHistoryKeep (polynomialRangeKeep t)) z := by
  rw [fullHistoryAmplitude_exact]
  simp only [formulaRangePolynomials_iff, formulaPolynomial_eval_update, formulaFourier_polynomial_eval]
  rfl

noncomputable def globalHistoryCoefficient {σ : Type*} {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (units : Fin steps.length → ℕ)
    (F : Fin n → HistoryFormula σ) (G : Fin t → HistoryFormula σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (glo ghi : Fin t → ℝ) (x : σ → ℤ) : ℂ :=
  (if ValidIntegerReconstruction steps x ∧
      ∀ i, IsUnit ((reconstructedPivotAt steps x i : ℤ) : ZMod (units i)) then 1 else 0) *
    globalHistoryArchCoefficient F G X ψ v lo hi glo ghi x

/-- No support representation is assumed here: the global coefficient is
identical to the polynomial coefficient used by the one-sided estimate. -/
theorem globalHistoryCoefficient_local {σ : Type*} {n t : ℕ}
    (steps : List (HistoryPivotStep σ)) (units : Fin steps.length → ℕ)
    (F : Fin n → HistoryFormula σ) (G : Fin t → HistoryFormula σ)
    (X : Fin n → ℝ) (ψ : 𝓢(ℝ, ℂ)) (v lo hi : Fin n → ℝ)
    (hlo : ∀ j, 1 ≤ lo j) (hhi : ∀ j, lo j ≤ hi j) (glo ghi : Fin t → ℝ)
    (a : σ → ℤ) (coord : σ) (z : ℤ) :
    globalHistoryCoefficient steps units F G X ψ v lo hi glo ghi (Function.update a coord z) =
      reconstructedHistoryAmplitude steps units a coord
        (formulaFourierFactors F (fun j => (a j : ℝ)) coord X ψ v lo hi hlo hhi)
        (fullHistoryPolynomials (formulaFourierFactors F (fun j => (a j : ℝ)) coord X ψ v lo hi hlo hhi)
          (formulaRangePolynomials G (fun j => (a j : ℝ)) coord glo ghi))
        (fullHistoryKeep (polynomialRangeKeep t)) z := by
  unfold globalHistoryCoefficient reconstructedHistoryAmplitude
  rw [globalHistoryArchCoefficient_local F G X ψ v lo hi hlo hhi glo ghi a coord z]

end Ostmann

end OAI
