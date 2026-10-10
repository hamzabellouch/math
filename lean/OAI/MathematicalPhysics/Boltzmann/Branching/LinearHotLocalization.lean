import OAI.MathematicalPhysics.Boltzmann.Branching.EuclideanKineticMap
import OAI.MathematicalPhysics.Boltzmann.Branching.CausalConvolution
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalizedGainSmoothingAE

namespace OAI

/-! # Localized GLPS resolvents for a bounded weighted linear mild equation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

def linearSource (q L : ℝ) (F g : ℝ × JetPrototype.Phase → ℝ)
    (z : Published.KineticPhase) : ℝ :=
  H q z.2*(g (z.1.1,phaseEquiv (z.1.2,z.2))-L*F (z.1.1,phaseEquiv (z.1.2,z.2)))

theorem linearSource_along (q L : ℝ) (F g : ℝ × JetPrototype.Phase → ℝ)
    (p : Velocity × Velocity) (t : ℝ) :
    linearSource q L F g (TransportCutoff.characteristic p t) =
      H q p.2*(g (t,JetBarrier.flight t (phaseEquiv p))-
        L*F (t,JetBarrier.flight t (phaseEquiv p))) := by
  change H q p.2*(g (t,phaseEquiv (flight t p))-L*F (t,phaseEquiv (flight t p))) = _
  rw [phaseEquiv_flight]

theorem smooth_linear_localized {q T L S : ℝ} (hT : 0 ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {F g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀ : Measurable f₀) (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ u, |g u| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)))
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ (TransportCutoff.characteristic p T)*density q F (TransportCutoff.characteristic p T) =
        ∫ t in 0..T, Real.exp (-(T-t))*
          (χ (TransportCutoff.characteristic p t)*linearSource q L F g (TransportCutoff.characteristic p t)+
            (transportDerivative χ (TransportCutoff.characteristic p t)+χ (TransportCutoff.characteristic p t))*
              density q F (TransportCutoff.characteristic p t)) := by
  have hd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hh := PositiveIntegral.localized_characteristic hT hf₀ hFm hgm hg hmild
    (fun p t => χ (TransportCutoff.characteristic (phaseEquiv.symm p) t))
    (fun p t => transportDerivative χ (TransportCutoff.characteristic (phaseEquiv.symm p) t))
    (fun p => (hχ.continuous.comp (characteristic_continuous _)).continuousOn)
    (fun p => ((transportDerivative_continuous hχ).comp (characteristic_continuous _)).continuousOn)
    (fun p t _ => hasDerivAt_along hd _ t)
  filter_upwards [phaseEquiv_measurePreserving.quasiMeasurePreserving.ae hh] with p hp
  simp only [phaseEquiv.symm_apply_apply] at hp
  rw [hzero p] at hp
  simp only [mul_zero,zero_mul,zero_add] at hp
  have hm := congrArg (fun z : ℝ => H q p.2*z) hp
  rw [← intervalIntegral.integral_const_mul] at hm
  calc
    _ = H q p.2*(χ (TransportCutoff.characteristic p T)*F (T,JetBarrier.flight T (phaseEquiv p))) := by
      rw [show TransportCutoff.characteristic p T = ((T,(flight T p).1),(flight T p).2) from rfl,density_along]
      dsimp [PhysicalLocalization.density,JetBarrier.flight]
      ring
    _ = _ := hm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [linearSource_along]
      rw [show TransportCutoff.characteristic p t = ((t,(flight t p).1),(flight t p).2) from rfl,density_along]
      dsimp [PhysicalLocalization.density,JetBarrier.flight]
      ring

theorem linear_resolvent {q T U L S : ℝ} (hT : 0 ≤ T) (hTU : T ≤ U)
    {f₀ : JetPrototype.Phase → ℝ} {F g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀ : Measurable f₀) (hFm : Measurable F) (hgm : Measurable g)
    (hg : ∀ u, |g u| ≤ S)
    (hmild : ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)))
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ ((T,p.1),p.2)*density q F ((T,p.1),p.2) =
        Published.transportResolvent (localizedSource U χ (density q F) (linearSource q L F g))
          ((T,p.1),p.2) := by
  have h := smooth_linear_localized (q := q) hT hf₀ hFm hgm hg hmild hχ hzero
  filter_upwards [(flight_measurePreserving (-T)).quasiMeasurePreserving.ae h] with p hp
  simp only [characteristic_endpoint,characteristic_back] at hp
  rw [TransportPrimitive.transportResolvent_eq
    (fun z hz => localizedSource_causal U χ _ _ z hz) _ hT,hp]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  dsimp only
  rw [localizedSource_on χ _ _ _ ⟨ht.1,ht.2.trans hTU⟩]

end BoltzmannNonuniqueness.EuclideanFlight

end

end OAI
