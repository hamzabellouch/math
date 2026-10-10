import OAI.Analysis.CoulombTransport.FirstCoordinateLift

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356

/-- Arbitrarily small first-coordinate lifts of a uniformly separated optimal
coupling give finite Monge approximation. Only the first coordinate is adjusted
to obtain a graph, and uniform separation controls the cost of that adjustment. -/
theorem finiteMongeApproximation_of_near_fst_lifts
    {mu : Measure E3} [IsProbabilityMeasure mu] {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t)
    (hlifts : ∀ delta : ℝ, 0 < delta →
      ∃ Q : E3 → Triple, Measurable Q ∧ Measure.map Q mu = pi ∧
        ∀ᵐ x ∂mu, dist x (Q x).1 ≤ delta) :
    FiniteMongeApproximation mu := by
  intro epsilon hepsilon
  let delta : ℝ := min (eta / 2) (epsilon * eta ^ 2 / 24)
  have hdelta : 0 < delta := by
    dsimp [delta]
    apply lt_min
    · positivity
    · positivity
  obtain ⟨Q, hQ, hmap, hclose⟩ := hlifts delta hdelta
  have hdelta_eta : delta ≤ eta / 2 := min_le_left _ _
  obtain ⟨h2, h3, hfinite, hcost⟩ :=
    FirstCoordinateLift.graph_cost_of_lift hpi hQ hmap heta hdelta_eta hseparated hclose
  refine ⟨tripleSnd ∘ Q, tripleThd ∘ Q, h2, h3, hfinite, ?_⟩
  have herror : 24 * delta / eta ^ 2 ≤ epsilon := by
    apply (div_le_iff₀ (sq_pos_of_pos heta)).2
    have hdelta_eps : delta ≤ epsilon * eta ^ 2 / 24 := min_le_right _ _
    linarith
  calc
    graphCost mu (tripleSnd ∘ Q) (tripleThd ∘ Q) ≤
        (∫⁻ t, coulombCost t ∂pi) + ENNReal.ofReal (24 * delta / eta ^ 2) := hcost
    _ ≤ kantorovichValue mu + ENNReal.ofReal epsilon := by
      rw [hoptimal]
      exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal herror)

/-- A uniformly separated optimal coupling has finite value. -/
theorem kantorovichValue_lt_top_of_separated_optimizer
    {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    kantorovichValue mu < ⊤ := by
  have : IsProbabilityMeasure pi := hpi.1
  rw [← hoptimal]
  exact CoulombEstimates.lintegral_coulombCost_lt_top_of_ae_separated pi heta hseparated

end Problem356

end

end OAI
