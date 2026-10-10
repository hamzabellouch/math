import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Every feasible Monge pair bounds its defining infimum from above. -/
theorem mongeValue_le_graphCost (mu : Measure E3) {T2 T3 : E3 → E3}
    (h2 : Preserves mu T2) (h3 : Preserves mu T3) :
    mongeValue mu ≤ graphCost mu T2 T3 := by
  exact iInf_le_of_le T2 (iInf_le_of_le T3 (iInf_le_of_le h2 (iInf_le _ h3)))

/-- Arbitrarily accurate finite preserving-map approximations imply equality of values. -/
theorem FiniteMongeApproximation.equal_infima {mu : Measure E3}
    [IsProbabilityMeasure mu] (h : FiniteMongeApproximation mu) :
    mongeValue mu = kantorovichValue mu := by
  apply le_antisymm _ (kantorovichValue_le_mongeValue mu)
  apply ENNReal.le_of_forall_pos_le_add
  intro epsilon hepsilon _
  obtain ⟨T2, T3, h2, h3, _, hcost⟩ := h epsilon hepsilon
  exact (mongeValue_le_graphCost mu h2 h3).trans (by simpa using hcost)

/-- Finite equality of values already supplies finite near-minimizing preserving maps. -/
theorem finiteMongeApproximation_of_equal_infima {mu : Measure E3}
    (hfinite : kantorovichValue mu < ⊤)
    (heq : mongeValue mu = kantorovichValue mu) :
    FiniteMongeApproximation mu := by
  intro epsilon hepsilon
  have hlt : mongeValue mu < kantorovichValue mu + ENNReal.ofReal epsilon := by
    rw [heq]
    exact ENNReal.lt_add_right hfinite.ne
      (ne_of_gt (ENNReal.ofReal_pos.mpr hepsilon))
  unfold mongeValue at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨T2, T3, h2, h3, hcost⟩ := hlt
  refine ⟨T2, T3, h2, h3, ?_, hcost.le⟩
  exact hcost.trans (ENNReal.add_lt_top.mpr ⟨hfinite, ENNReal.ofReal_lt_top⟩)

/-- Under finiteness, equal infima and finite Monge approximation are equivalent. -/
theorem finiteMongeApproximation_iff_equal_infima {mu : Measure E3}
    [IsProbabilityMeasure mu] (hfinite : kantorovichValue mu < ⊤) :
    FiniteMongeApproximation mu ↔ mongeValue mu = kantorovichValue mu :=
  ⟨FiniteMongeApproximation.equal_infima, finiteMongeApproximation_of_equal_infima hfinite⟩

/-- The full target conclusion follows once the counterexample and finite approximation
have been constructed for the same density. -/
theorem HasCoulombCounterexample.fullConclusion {rho : E3 → ℝ}
    (h : HasCoulombCounterexample rho)
    (happrox : FiniteMongeApproximation (densityMeasure rho)) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := h.2.1
  exact ⟨h, happrox.equal_infima, happrox⟩

end Problem356

end

end OAI
