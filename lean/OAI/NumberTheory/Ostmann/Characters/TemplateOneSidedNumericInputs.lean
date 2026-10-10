import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsAtoms
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsRows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedNumericInputs
open Filter Preliminaries

theorem eventually_linear_frequency_height (a z β : ℝ) (ha : 0 ≤ a)
    (hz : 0 ≤ z) (hβ : 0 < β) :
    ∀ᶠ L : ℝ in atTop, ∀ C : ℝ, 0 ≤ C →
      a*(⌊z*L⌋₊:ℝ) ≤ rowLogHeight C z β L := by
  filter_upwards [eventually_historyPolynomialCost_le a z 1 hz hβ
    (by norm_num : (0:ℝ)<1)] with L hL
  intro C hC
  have haL : a*(⌊z*L⌋₊:ℝ) ≤ Real.exp (β*L) := by
    have hm : a*(⌊z*L⌋₊:ℝ) ≤ a*(1+(⌊z*L⌋₊:ℝ)) := by nlinarith
    exact hm.trans (by simpa only [historyPolynomialCost,pow_one,one_mul] using hL)
  have hc : 0 ≤ historyPolynomialCost C z 3 L := by
    unfold historyPolynomialCost
    positivity
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold rowLogHeight
  linarith

theorem eventually_original_source_numeric_inputs
    (C CD a c z α β W : ℝ) (hC : 0 ≤ C) (hCD : 0 ≤ CD) (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hz : 0 < z) (hα : 0 < α) (hβ : 0 ≤ β) :
    ∃ C' : ℝ,0 < C' ∧ ∀ᶠ L : ℝ in atTop,
      (∀ {N : ℕ} (E : Finset (PrimeUpTo N)) (hE : 0 < primeShellMass E),
        Real.exp (-c*L) ≤ primeShellMass E →
        (∀p∈E,Real.exp (α*L) ≤ Real.log p.val) →
        ∀p,(primeShellPrior E hE).mass p ≤ Real.exp (-(1/2:ℝ)*Real.exp (α*L))) ∧
      (∀ Q p : ℕ,(Q:ℝ) ≤ Real.exp (historyPolynomialCost C z 3 L) →
        Real.exp (α*L) ≤ Real.log p → Q < p) ∧
      Real.log 2 ≤ rowLogHeight C z β L ∧
      rowLogHeight C z β L ≤ Real.exp (historyPolynomialCost C' z 4 L) ∧
      (∀ D : ℝ,0 ≤ D → D ≤ CD*(1+(⌊z*L⌋₊:ℝ)) →
        D*rowLogHeight C z β L+|a*(⌊z*L⌋₊:ℝ)|+|W| ≤
          Real.exp (historyPolynomialCost C' z 4 L)) := by
  refine ⟨numericCostCoefficient β z C CD a W,(numeric_inputs_cost W hβ hz hC hCD ha).1,?_⟩
  filter_upwards [eventually_primeShellPrior_mass_le hα hc,
    eventually_budget_modulus_lt_prime C z 3 hz.le hα] with L hatom hprime
  exact ⟨hatom,hprime,rowLogHeight_ge_log_two C z β L hC,
    (numeric_inputs_cost W hβ hz hC hCD ha).2 L⟩

end Ostmann.Characters.TemplateOneSidedNumericInputs

end

end OAI
