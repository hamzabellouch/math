import OAI.Analysis.CoulombTransport.CellwiseLift
import OAI.Analysis.CoulombTransport.SeparatedLiftApproximation
import OAI.Analysis.CoulombTransport.DensityMeasure
import OAI.Analysis.CoulombTransport.EqualInfima

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Problem356

/-- A compactly supported atomless marginal and a uniformly separated optimal
coupling admit finite-cost deterministic approximations. -/
theorem finiteMongeApproximation_of_compact_separated_optimizer
    {mu : Measure E3} [IsProbabilityMeasure mu] [NullSingletonClass mu]
    {pi : Measure Triple} (hpi : IsThreeCoupling mu pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue mu)
    {K : Set E3} (hK : IsCompact K) (hfull : mu Kᶜ = 0)
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    FiniteMongeApproximation mu := by
  have : IsProbabilityMeasure pi := hpi.1
  apply finiteMongeApproximation_of_near_fst_lifts hpi hoptimal heta hseparated
  intro delta hdelta
  obtain ⟨Q, hQ, hmap, hclose⟩ := Transport.exists_measurable_lift_close
    mu pi tripleFst measurable_tripleFst hpi.2.1 hK hfull hdelta
  exact ⟨Q, hQ, hmap, hclose.mono fun _ hx => hx.le⟩

/-- A Coulomb counterexample with a separated optimal plan and compactly supported
density has equal Monge and Kantorovich infima and finite-cost Monge approximations. -/
theorem HasCoulombCounterexample.hasFull_of_separated_optimizer
    {rho : E3 → ℝ} (hcounter : HasCoulombCounterexample rho)
    {pi : Measure Triple} (hpi : IsThreeCoupling (densityMeasure rho) pi)
    (hoptimal : (∫⁻ t, coulombCost t ∂pi) = kantorovichValue (densityMeasure rho))
    {eta : ℝ} (heta : 0 < eta)
    (hseparated : ∀ᵐ t ∂pi, CoulombEstimates.Separated eta t) :
    HasFullCoulombConclusion rho := by
  have : IsProbabilityMeasure (densityMeasure rho) := hcounter.2.1
  obtain ⟨K, hK, hfull⟩ := densityMeasure_exists_compact_conull hcounter.1.2.2.1
  have happ := finiteMongeApproximation_of_compact_separated_optimizer
    hpi hoptimal hK hfull heta hseparated
  exact hcounter.fullConclusion happ

end Problem356

end

end OAI
