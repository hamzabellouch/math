import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Finite graph approximants give the reverse relaxation inequality, hence
identify the Monge and Kantorovich infima. -/
theorem mongeValue_eq_kantorovichValue_of_finiteMongeApproximation
    (mu : Measure E3) [IsProbabilityMeasure mu] (happrox : FiniteMongeApproximation mu) :
    mongeValue mu = kantorovichValue mu := by
  apply le_antisymm ?_ (kantorovichValue_le_mongeValue mu)
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  have hepsilon' : (0 : ℝ) < epsilon := by exact_mod_cast hepsilon
  obtain ⟨T2, T3, h2, h3, _hfinite, hcost⟩ := happrox epsilon hepsilon'
  have hmonge : mongeValue mu ≤ graphCost mu T2 T3 := by
    unfold mongeValue
    exact iInf_le_of_le T2 (iInf_le_of_le T3
      (iInf_le_of_le h2 (iInf_le_of_le h3 le_rfl)))
  exact hmonge.trans (by simpa using hcost)

/-- The final logical closure: counterexample construction plus finite Monge
approximation gives the complete qualified conclusion without changing any
of its predicates. -/
theorem hasFullCoulombConclusion_of_counterexample_of_approximation
    {rho : E3 → ℝ} (hcounter : HasCoulombCounterexample rho)
    (happrox : FiniteMongeApproximation (densityMeasure rho)) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := hcounter.2.1
  exact ⟨hcounter,
    mongeValue_eq_kantorovichValue_of_finiteMongeApproximation (densityMeasure rho) happrox,
    happrox⟩

end Problem356

end

end OAI
