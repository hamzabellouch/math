import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedNetLoss
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting

namespace OAI

/-! # Extending a mild representative constantly beyond its time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

def clampTime (T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  F (PositiveIntegral.time T u.1,u.2)

theorem measurable_clampTime {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (T : ℝ) :
    Measurable (clampTime T F) := by
  apply hFm.comp
  unfold PositiveIntegral.time
  fun_prop

theorem forcing_clampTime (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) :
    forcing q b L (clampTime T F) u = forcing q b L F (PositiveIntegral.time T u.1,u.2) := rfl

theorem mildAE_all_times {q b L T : ℝ} (hT : 0 ≤ T) {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ} (hF : MildAE q b L T f₀ F) :
    ∀ t, (fun p => clampTime T F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀
        (forcing q b L (clampTime T F)) (t,p)) := by
  have hs : ∀ r ∈ Icc 0 T, ∀ p,
      forcing q b L (clampTime T F) (r,p) = forcing q b L F (r,p) := by
    intro r hr p
    rw [forcing_clampTime,GaussianLocal.time_eq hr]
  intro t
  filter_upwards [hF (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)] with p hp
  change F (PositiveIntegral.time T t,p) = _
  rw [PositiveIntegral.value_eq_of_time_eq hT L f₀ hs (t,p)]
  rw [← PositiveIntegral.value_time_clamp hT L f₀ (forcing q b L F) (t,p)]
  exact hp

end BoltzmannNonuniqueness.WeightedLocal

end

end OAI
