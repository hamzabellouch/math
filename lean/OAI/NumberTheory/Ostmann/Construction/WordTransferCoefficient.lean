import OAI.NumberTheory.Ostmann.Construction.WordTransferArrays

namespace OAI

/-! # The constructed coefficient for a branching word history -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

structure WordFourierParameters (n : ℕ) where
  scale : Fin (2 ^ n) → ℝ
  profile : 𝓢(ℝ, ℂ)
  lower : Fin (2 ^ n) → ℝ
  upper : Fin (2 ^ n) → ℝ
  lower_one : ∀ i, 1 ≤ lower i
  lower_upper : ∀ i, lower i ≤ upper i

namespace WordFourierParameters

variable {σ : Type*} {n : ℕ}

noncomputable def frequency (_p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (i : Fin (2 ^ n)) : ℝ :=
  let z := template.leafAt t hn i
  if z.positive then (z.frequency : ℝ) else -(z.frequency : ℝ)

noncomputable def factors (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :
    Fin (2 ^ n) → ClippedPolynomialFactor :=
  formulaFourierFactors (fun i => (template.leafAt t hn i).formula) (fun i => (a i : ℝ)) coord
    p.scale p.profile (p.frequency template t hn) p.lower p.upper p.lower_one p.lower_upper

noncomputable def polynomials (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :=
  fullHistoryPolynomials (p.factors template t hn a coord)
    (wordGuardPolynomials (template.guardAt t hn) a coord)

noncomputable def keep (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :=
  fullHistoryKeep (n := 2 ^ n) (wordGuardKeep (template.guardAt t hn))

noncomputable def budget (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) : ℝ :=
  formulaFourierBudget p.profile (p.frequency template t hn) p.lower p.upper

noncomputable def coefficient (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (x : σ → ℤ) : ℂ :=
  (if (∀ i, (template.guardAt t hn i).ValidAt x) ∧
      (∀ j, (template.leafAt t hn j).formula.realValue x / p.scale j ∈ Set.Icc (p.lower j) (p.upper j))
    then 1 else 0) *
      ∏ j, normalizedFourierProfile p.profile (p.frequency template t hn j)
        ((template.leafAt t hn j).formula.realValue x / p.scale j)

/-- No representation hypothesis is needed: these are the exact polynomial
and residue gates constructed from the original branching data. -/
theorem coefficient_local (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    p.coefficient template t hn (Function.update a coord z) =
      guardedHistoryAmplitude (wordGuardNumerators (template.guardAt t hn))
        (wordGuardDenominators (template.guardAt t hn)) (wordGuardModuli (template.guardAt t hn))
        a coord (p.factors template t hn a coord) (p.polynomials template t hn a coord)
        (keep template t hn) z := by
  have hs := wordGuard_family_support (template.guardAt t hn) a coord z
  simp only [coefficient, factors, polynomials, keep, guardedHistoryAmplitude,
    fullHistoryAmplitude_exact, formulaFourier_polynomial_eval]
  have he : (∏ j, ((formulaFourierFactors (fun i => (template.leafAt t hn i).formula)
      (fun i => (a i : ℝ)) coord p.scale p.profile (p.frequency template t hn) p.lower p.upper
      p.lower_one p.lower_upper) j).profile
        ((template.leafAt t hn j).formula.realValue (Function.update a coord z) / p.scale j)) =
      ∏ j, normalizedFourierProfile p.profile (p.frequency template t hn j)
        ((template.leafAt t hn j).formula.realValue (Function.update a coord z) / p.scale j) := rfl
  rw [he]
  simp only [formulaFourierFactors, historyFourierFactor, fourierPolynomialFactor]
  split_ifs <;> simp_all

theorem factors_budget (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ) :
    smoothPolynomialBudget (p.factors template t hn a coord) = p.budget template t hn := rfl

theorem budget_nonneg (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) :
    0 ≤ p.budget template t hn :=
  formulaFourierBudget_nonneg _ _ _ _ p.lower_upper

/-- The complete partition complexity is polynomial in the word size for
fixed depth, including every original support inequality. -/
theorem complexity_bound (p : WordFourierParameters n) (template : WordTransferTemplate σ n)
    (t : FrequencyTree ℤ n) (hn : NonzeroInternalFrequencies n t) (a : σ → ℤ) (coord : σ)
    (B : ℕ) (hB : 1 ≤ B) (hwords : template.WordsBounded B) :
    polynomialWeightComplexity (p.factors template t hn a coord) (p.polynomials template t hn a coord) ≤
      (3 * 2 ^ n + 3 * (2 ^ n - 1)) * B ^ (n + 1) := by
  have hl : (∑ i, ((p.factors template t hn a coord) i).polynomial.natDegree) ≤
      2 ^ n * B ^ (n + 1) := by
    calc
      _ ≤ ∑ _i : Fin (2 ^ n), B ^ (n + 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact (formulaFourierFactors_degree _ _ _ _ _ _ _ _ _ _ i).trans
          (template.leafAt_cost t hn B hB hwords i)
      _ = _ := by simp
  have hg : (∑ i, max (template.guardAt t hn i).pivot.cost
      (template.guardAt t hn i).rightProduct.cost) ≤ (2 ^ n - 1) * B ^ (n + 1) := by
    calc
      _ ≤ ∑ _i : Fin (2 ^ n - 1), B ^ (n + 1) :=
        Finset.sum_le_sum fun i _ => template.guardAt_cost t hn B hB hwords i
      _ = _ := by simp
  have hguard := wordGuard_family_degree (template.guardAt t hn) a coord
  apply (fullHistoryPolynomials_complexity (p.factors template t hn a coord)
    (wordGuardPolynomials (template.guardAt t hn) a coord)).trans
  nlinarith

end WordFourierParameters
end Ostmann

end OAI
