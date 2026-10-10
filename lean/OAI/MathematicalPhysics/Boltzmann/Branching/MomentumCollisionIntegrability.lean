import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation

namespace OAI

/-! # Integrability of each momentum component of gain and loss -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem gainLoss_coordinate_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (he : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (i : Fin 3) :
    Integrable (fun p => p.2 i*gainDensity f p) (μ.prod volume) ∧
      Integrable (fun p => p.2 i*lossDensity f p) (μ.prod volume) := by
  have h := momentum_rate_integrable hfm hfn hp he i
  exact ⟨(collision_test_marginal (postRate f) (fun p => p.2 i) h.2).1,
    (collision_test_marginal (preRate f) (fun p => p.2 i) h.1).1⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
