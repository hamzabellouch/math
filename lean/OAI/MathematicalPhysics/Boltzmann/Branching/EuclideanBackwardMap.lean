import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotUndamped
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveVolterra
import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.LinearHotLocalization

namespace OAI

section

/-! # Physical Euclidean transport tested along almost every characteristic -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem smooth_linear_tested {q T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {F g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀ : Measurable f₀) (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ u, |g u| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)))
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0)
    (hterminal : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p T) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      (∫ t in 0..T, transportDerivative χ (TransportCutoff.characteristic p t)*density q F (TransportCutoff.characteristic p t)+
        χ (TransportCutoff.characteristic p t)*linearSource q L F g (TransportCutoff.characteristic p t)) = 0 := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hh := PositiveIntegral.tested_characteristic hT hf₀ hFm hgm hg hmild
    (fun p t => χ (TransportCutoff.characteristic (phaseEquiv.symm p) t))
    (fun p t => transportDerivative χ (TransportCutoff.characteristic (phaseEquiv.symm p) t))
    (fun p => (hχ.continuous.comp (characteristic_continuous _)).continuousOn)
    (fun p => ((transportDerivative_continuous hχ).comp (characteristic_continuous _)).continuousOn)
    (fun p t _ => hasDerivAt_along hd _ t)
  filter_upwards [phaseEquiv_measurePreserving.quasiMeasurePreserving.ae hh] with p hp
  simp only [phaseEquiv.symm_apply_apply,hzero p,hterminal p,zero_mul,sub_self] at hp
  have hm := congrArg (fun z : ℝ => H q p.2*z) hp
  rw [mul_zero,← intervalIntegral.integral_const_mul] at hm
  calc
    _ = ∫ t in 0..T, H q p.2*
        (transportDerivative χ (TransportCutoff.characteristic p t)*F (t,JetBarrier.flight t (phaseEquiv p))+
          χ (TransportCutoff.characteristic p t)*(g (t,JetBarrier.flight t (phaseEquiv p))-
            L*F (t,JetBarrier.flight t (phaseEquiv p)))) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [linearSource_along]
      rw [show TransportCutoff.characteristic p t = ((t,(flight t p).1),(flight t p).2) from rfl,density_along]
      dsimp [PhysicalLocalization.density,JetBarrier.flight]
      ring
    _ = 0 := hm

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The spatial windows transported to Euclidean coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.EuclideanFlight

def hotBaseSet (A R : ℝ) : Set Published.SpaceTime :=
  Icc 0 A ×ˢ (spaceEquiv ⁻¹' Metric.closedBall (0 : JetPrototype.Space) R)

theorem hotBaseSet_measurable (A R : ℝ) : MeasurableSet (hotBaseSet A R) :=
  measurableSet_Icc.prod (measurableSet_closedBall.preimage spaceEquiv.measurable)

theorem hotBaseVolume_eq (A R : ℝ) : hotBaseVolume A R = volume.restrict (hotBaseSet A R) := by
  rw [hotBaseVolume,Measure.prod_restrict,← Measure.volume_eq_prod]
  rfl

theorem hotBaseSet_time (A R : ℝ) : hotBaseSet A R ⊆ Icc 0 A ×ˢ univ :=
  fun _ h => ⟨h.1,mem_univ _⟩

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Backward positive-iteration paths in the physical jet coordinates -/

noncomputable section

open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem backward_kineticMap (p : Velocity × Velocity) (t s : ℝ) :
    kineticMap (PositiveIteration.flight ((t,p.1),p.2) s) =
      (s,JetBarrier.flight s (phaseEquiv (flight (-t) p))) := by
  have hp : flight s (flight (-t) p) = (p.1-(t-s) • p.2,p.2) := by
    apply Prod.ext
    · dsimp [flight]
      module
    · rfl
  change (s,phaseEquiv (p.1-(t-s) • p.2,p.2)) = _
  rw [← hp,phaseEquiv_flight]

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
