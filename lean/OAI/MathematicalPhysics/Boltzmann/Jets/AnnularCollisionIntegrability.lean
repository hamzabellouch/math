import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWeakMarginals
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTailRegions

namespace OAI

/-! # Collision-pair uniform integrability from the proved annular envelopes -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AnnularEnvelope

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem annular_pairs_uniformIntegrable {s₀ η T q A B : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T)
    (hq : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {f : ℕ → (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hmoment : ∀ n, ∀ᵐ u ∂timePositionVolume T,
      VelocityMoment.moment (fun v => f n (u,v)) ≤
        ENNReal.ofReal (commonMoment s₀ η A B (torusChart u)))
    (houter : ∀ J : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ n,
      ∀ᵐ u ∂timePositionVolume T, ∀ᵐ v : Velocity,
        u ∉ torusTail s₀ η J → f n (u,v) ≤ D*H q v) :
    UniformIntegrable (fun n => pairDensity (f n)) 1
      ((timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) := by
  classical
  choose D hD hDom using houter
  exact collision_pairs_uniformIntegrable hq hfm hf
    (fun u => commonMoment_nonneg hA hB s₀ η (torusChart u)) hmoment
    (torusTail_measurable s₀ η) hD hDom
    (common_collision_tail_tendsto hs₀ hη hηmax hT A B)

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
