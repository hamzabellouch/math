import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralBound
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedColdFiniteLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions

namespace OAI

section

/-! # Cold-core survival for the a.e. representatives in the actual cap construction -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem ColdMildAE.survival {q b L T R t : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (hceq : ColdMildAE q b L T F c₀ c) (ht : t ∈ Icc 0 T)
    (E k : JetPrototype.Phase → ℝ → ℝ)
    (hE : ∀ p, ContDiff ℝ 1 (E p)) (hE' : ∀ p r, HasDerivAt (E p) (k p r) r)
    (hν : ∀ᵐ p ∂FlightMeasure.phaseVolume, c₀ p ≠ 0 → ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) t),
      CollisionCutoff.frequency b (fun v => physical q F (r,((JetBarrier.flight r p).1,v))) p.2 ≤ k p r) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (E p 0-E p t)*c₀ p ≤ c (t,JetBarrier.flight t p) := by
  have hpath := PositiveIntegral.ae_characteristic_path ht hc₀m hcm
    (measurable_coldForcing hFm hcm q b L) hceq
  filter_upwards [hpath,hν] with p hp hνp
  by_cases hpzero : c₀ p = 0
  · rw [hpzero,mul_zero]
    exact (hc (t,JetBarrier.flight t p)).1
  have hνp := hνp hpzero
  let g : ℝ → ℝ := fun r => coldForcing q b L F c (r,JetBarrier.flight r p)
  let S : ℝ := HotApplication.realBound q*R^2+L*R
  have hgb (r : ℝ) : 0 ≤ g r ∧ g r ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hcm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hc (p.1.1,(p.1.2,p.2))) _
  have hgm : Measurable g := (measurable_coldForcing hFm hcm q b L).comp
    (measurable_id.prodMk (GaussianLocal.measurable_flight.comp
      (measurable_id.prodMk measurable_const)))
  have hgi : IntervalIntegrable g volume 0 t := by
    apply (intervalIntegrable_const (c := S)).mono_fun' hgm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun r => by
      change ‖g r‖ ≤ S
      rw [Real.norm_eq_abs,abs_of_nonneg (hgb r).1]
      exact (hgb r).2)
  have hpe := hp.1
  change ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) t), c (r,JetBarrier.flight r p) =
    TransportPrimitive.damped L (c₀ p) g r at hpe
  rw [ae_restrict_iff' measurableSet_Icc] at hpe hνp
  have hbound : ∀ᵐ r, r ∈ Icc 0 t →
      (L-k p r)*TransportPrimitive.damped L (c₀ p) g r ≤ g r := by
    filter_upwards [hpe,hνp] with r hpr hνr hr
    rw [← hpr hr]
    have hgain := HotRepresentative.gain_nonneg
      (fun p => (hc (p.1.1,(p.1.2,p.2))).1) q b ((r,(JetBarrier.flight r p).1),p.2)
    change 0 ≤ HotRepresentative.gain q b (GaussianLocal.state c)
      ((r,(JetBarrier.flight r p).1),p.2) at hgain
    change (L-k p r)*c (r,JetBarrier.flight r p) ≤
      HotRepresentative.gain q b (GaussianLocal.state c) ((r,(JetBarrier.flight r p).1),p.2)+
        (L-CollisionCutoff.frequency b (fun v => physical q F
          (r,((JetBarrier.flight r p).1,v))) p.2)*c (r,JetBarrier.flight r p)
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left (hνr hr) L)
      (hc (r,JetBarrier.flight r p)).1).trans (le_add_of_nonneg_left hgain)
  rw [hp.2]
  exact TransportPrimitive.damped_survival ht.1 hgi (hE p) (hE' p) hbound

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Weak transport equation for the actual positive periodic approximations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem weak_characteristic {q b L T R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L T R f₀) (hq : q < 2) (hb : 0 ≤ b)
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hf₀ : Measurable f₀) {ψ ψ' : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Icc 0 T)) (hψ' : ContinuousOn ψ' (Icc 0 T))
    (hdψ : ∀ t ∈ Icc 0 T, HasDerivAt ψ (ψ' t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      (∫ t in 0..T, ψ' t*F.value (t,JetBarrier.flight t p) +
        ψ t*(forcing q b L F.value (t,JetBarrier.flight t p)-
          L*F.value (t,JetBarrier.flight t p))) =
        ψ T*F.value (T,JetBarrier.flight T p)-ψ 0*f₀ p := by
  refine PositiveIntegral.weak_characteristic (S := HotApplication.realBound q*R^2+L*R)
    hT hf₀ F.measurable_value (measurable_forcing F.measurable_value q b L) ?_
    F.mild hψ hψ' hdψ
  intro z
  have h := HotRepresentative.source_bounds hq hb hR hloss
    (GaussianLocal.measurable_state F.measurable_value)
    (fun p => F.value_bounds (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
  change 0 ≤ forcing q b L F.value z ∧
    forcing q b L F.value z ≤ HotApplication.realBound q*R^2+L*R at h
  rw [abs_of_nonneg h.1]
  exact h.2

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

end OAI
