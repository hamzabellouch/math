import Mathlib
import OAI.Probability.Ballisticity.Coupling.FreshBudgetEvent

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem adapted_initial_clipping {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (k : ℕ) {T η ε : ℝ} (hT : 0<T) (hη : 0<η) (hε : 0<ε) :
    ∃ g : ℝ, 0<g ∧ ∃ R : ℝ, 0<R ∧ ∀ ρ : ℝ, R≤ρ →
      ∀ H : ℕ, (H:ℝ)≤T*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ →
      ∀ (a G : ℝ) (π : Environment d → BudgetProfile (k:=k) e f a G),
      @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] E →
        environmentLaw ν (E∩{ω | relativeBudgetMass e f H (η*ρ) (π ω).val ω<g})≤
          ENNReal.ofReal ε*environmentLaw ν E := by
  obtain ⟨g,hg,R,hR,hh⟩ := initial_relativeBudget_clipping ν hue e f hef htrans k hT hη hε
  refine ⟨g,hg,R,hR,fun ρ hρ H hH a G π hπ E hE => ?_⟩
  apply fresh_random_budget_mass_lt ν e f a G (η*ρ) g H π hπ E hE (ENNReal.ofReal ε)
  intro θ _
  have h := hh ρ hρ H (π θ).val (π θ).property.1 hH
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal h.le

end DirectionalTransience

end

end OAI
