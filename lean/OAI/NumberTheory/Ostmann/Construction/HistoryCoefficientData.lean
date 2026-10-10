import OAI.NumberTheory.Ostmann.Arithmetic.GlobalHistoryCoefficient

namespace OAI

/-! # The finite data of one fully substituted history coefficient -/

namespace Ostmann

open scoped BigOperators SchwartzMap Classical

structure HistoryCoefficientData (σ : Type*) where
  leafCount : ℕ
  rangeCount : ℕ
  steps : List (HistoryPivotStep σ)
  units : Fin steps.length → ℕ
  leaves : Fin leafCount → HistoryFormula σ
  ranges : Fin rangeCount → HistoryFormula σ
  scale : Fin leafCount → ℝ
  fourier : 𝓢(ℝ, ℂ)
  frequency : Fin leafCount → ℝ
  lower : Fin leafCount → ℝ
  upper : Fin leafCount → ℝ
  lower_one : ∀ i, 1 ≤ lower i
  lower_upper : ∀ i, lower i ≤ upper i
  rangeLower : Fin rangeCount → ℝ
  rangeUpper : Fin rangeCount → ℝ

namespace HistoryCoefficientData

variable {σ : Type*}

noncomputable def value (d : HistoryCoefficientData σ) (x : σ → ℤ) : ℂ :=
  globalHistoryCoefficient d.steps d.units d.leaves d.ranges d.scale d.fourier
    d.frequency d.lower d.upper d.rangeLower d.rangeUpper x

noncomputable def factors (d : HistoryCoefficientData σ) (a : σ → ℤ) (coord : σ) :
    Fin d.leafCount → ClippedPolynomialFactor :=
  formulaFourierFactors d.leaves (fun i => (a i : ℝ)) coord d.scale d.fourier
    d.frequency d.lower d.upper d.lower_one d.lower_upper

noncomputable def polynomials (d : HistoryCoefficientData σ) (a : σ → ℤ) (coord : σ) :
    Fin ((d.leafCount + d.leafCount) + (d.rangeCount + d.rangeCount)) → Polynomial ℝ :=
  fullHistoryPolynomials (d.factors a coord)
    (formulaRangePolynomials d.ranges (fun i => (a i : ℝ)) coord d.rangeLower d.rangeUpper)

noncomputable def keep (d : HistoryCoefficientData σ) :
    (Fin ((d.leafCount + d.leafCount) + (d.rangeCount + d.rangeCount)) → Bool) → Bool :=
  fullHistoryKeep (polynomialRangeKeep d.rangeCount)

noncomputable def budget (d : HistoryCoefficientData σ) : ℝ :=
  formulaFourierBudget d.fourier d.frequency d.lower d.upper

def complexity (d : HistoryCoefficientData σ) : ℕ :=
  3 * (∑ j, (d.leaves j).cost) + 2 * ∑ j, (d.ranges j).cost

theorem budget_nonneg (d : HistoryCoefficientData σ) : 0 ≤ d.budget :=
  formulaFourierBudget_nonneg d.fourier d.frequency d.lower d.upper d.lower_upper

theorem factors_budget (d : HistoryCoefficientData σ) (a : σ → ℤ) (coord : σ) :
    smoothPolynomialBudget (d.factors a coord) = d.budget := rfl

theorem polynomials_complexity (d : HistoryCoefficientData σ) (a : σ → ℤ) (coord : σ) :
    polynomialWeightComplexity (d.factors a coord) (d.polynomials a coord) ≤ d.complexity :=
  formulaFourier_full_complexity d.leaves d.ranges (fun i => (a i : ℝ)) coord
    d.scale d.fourier d.frequency d.lower d.upper d.lower_one d.lower_upper d.rangeLower d.rangeUpper

theorem value_local (d : HistoryCoefficientData σ) (a : σ → ℤ) (coord : σ) (z : ℤ) :
    d.value (Function.update a coord z) =
      reconstructedHistoryAmplitude d.steps d.units a coord (d.factors a coord)
        (d.polynomials a coord) d.keep z :=
  globalHistoryCoefficient_local d.steps d.units d.leaves d.ranges d.scale d.fourier
    d.frequency d.lower d.upper d.lower_one d.lower_upper d.rangeLower d.rangeUpper a coord z

end HistoryCoefficientData
end Ostmann

end OAI
