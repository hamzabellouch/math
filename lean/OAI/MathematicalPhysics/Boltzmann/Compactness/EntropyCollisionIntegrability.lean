import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicJointBudgetLimit

namespace OAI

/-! # Separate collision integrability from entropy and dissipation budgets -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem normalized_collisions_of_entropy {g : X × Velocity → ℝ}
    (hgm : Measurable g) (hgn : ∀ p, 0 ≤ g p)
    (hE : Integrable (entropyGauge g) (μ.prod volume))
    (hD : rateDissipation μ g < ⊤) :
    Integrable (fun p => gainDensity g p/(1+g p/maxwellian p.2)) (μ.prod volume) ∧
    Integrable (fun p => lossDensity g p/(1+g p/maxwellian p.2)) (μ.prod volume) ∧
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      Integrable (fun q => postRate g (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q => preRate g (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) := by
  have hI := integrable_of_entropyGauge hgm hgn hE
  apply normalized_gainLoss_and_fibers hgm hgn hI _ hD
  have hL := linearMoment_integrable hgm hgn hE
  convert hL.sub hI using 1
  funext p
  simp only [linearMoment,Pi.sub_apply]
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
