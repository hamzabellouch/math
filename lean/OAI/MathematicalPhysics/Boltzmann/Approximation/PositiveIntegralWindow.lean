import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdTime

namespace OAI

/-! # Restarting an a.e. mild equation on a bounded time window -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

def window (s U : ℝ) (f : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  f (s+time U u.1,u.2)

theorem measurable_window (s U : ℝ) {f : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) : Measurable (window s U f) := by
  apply hfm.comp
  unfold time
  fun_prop

theorem window_clamped {U : ℝ} (hU : 0 ≤ U) (s : ℝ)
    (f : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    window s U f (time U u.1,u.2) = window s U f u := by
  change f (s+time U (time U u.1),u.2) = _
  rw [PhaseEssSup.time_idempotent hU]
  rfl

theorem window_mild_ae {T L S s U : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (hU : 0 ≤ U) (hsU : s+U ≤ T)
    {f : ℝ × JetPrototype.Phase → ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {g : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ u, |g u| ≤ S)
    (he : ∀ t ∈ Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ t, (fun p => window s U f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value U L JetBarrier.flight (fun p => f (s,p)) (window s U g) (t,p)) := by
  apply WeightedLocal.mild_all_of_time_clamp hU L (window_clamped hU s f)
  intro t ht
  have hst : s ≤ s+t := by linarith [ht.1]
  have htop : s+t ≤ T := by linarith [ht.2]
  have hi := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae
    (he s ⟨hs,by linarith⟩)
  filter_upwards [he (s+t) ⟨by linarith,htop⟩,hi] with p hp hip
  change f (s+time U t,p) = _
  rw [GaussianLocal.time_eq ht,hp]
  have hr := restart hT hL hs hst htop f₀ hgm hg p
  have hsimp : s-(s+t) = -t := by ring
  have hsub : s+t-s = t := by ring
  rw [hsimp,← hip,hsub] at hr
  rw [hr]
  have hv := shifted_value (s := s) (t := s+t)
    (show s+t-s ∈ Icc 0 U by simpa only [hsub] using ht) L
    (fun p => f (s,p)) (window s U g) p
  rw [hsub,hsimp] at hv
  rw [hv]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hrr
  rw [uIcc_of_le hst] at hrr
  change Real.exp (-L*(s+t-r))*g (r,JetBarrier.flight (r-(s+t)) p) =
    Real.exp (-L*(s+t-r))*g (s+time U (r-s),JetBarrier.flight (r-(s+t)) p)
  rw [GaussianLocal.time_eq (show r-s ∈ Icc 0 U by constructor <;> linarith [hrr.1,hrr.2,ht.2])]
  rw [add_sub_cancel]

end BoltzmannNonuniqueness.PositiveIntegral

end

end OAI
