import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCharacteristics
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPhysicalSource

namespace OAI

section

/-! # Physical collision source in the localized characteristic equation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.PhysicalLocalization

def density (q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) : ℝ := H q z.2.2*F z

def source (b q : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) : ℝ :=
  CollisionCompactness.collisionSource b (GaussianLocal.state (density q F)) ((z.1,z.2.1),z.2.2)

theorem source_eq {q b L : ℝ} (F : ℝ × JetPrototype.Phase → ℝ)
    {p : JetPrototype.Phase} (hp : p.2 ∈ HotRepresentative.good q) (t : ℝ) :
    H q p.2*(forcing q b L F (t,JetBarrier.flight t p)-L*F (t,JetBarrier.flight t p)) =
      source b q F (t,JetBarrier.flight t p) := by
  exact HotRepresentative.physical_source_eq (q := q) (b := b) (L := L) (GaussianLocal.state F)
    (p := ((t,(JetBarrier.flight t p).1),(JetBarrier.flight t p).2)) hp

/-- The constructed positive periodic solutions satisfy the physical localized
Duhamel formula; the artificial iteration damping has disappeared. -/
theorem localized (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    (χ χ' : JetPrototype.Phase → ℝ → ℝ)
    (hχ : ∀ p, ContinuousOn (χ p) (Icc 0 T))
    (hχ' : ∀ p, ContinuousOn (χ' p) (Icc 0 T))
    (hdχ : ∀ p t, t ∈ Icc 0 T → HasDerivAt (χ p) (χ' p t) t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      χ p T*density q F.value (T,JetBarrier.flight T p) =
        Real.exp (-T)*χ p 0*(H q p.2*f₀ p) +
        ∫ t in 0..T, Real.exp (-(T-t)) *
          (χ p t*source b q F.value (t,JetBarrier.flight t p) +
            (χ' p t+χ p t)*density q F.value (t,JetBarrier.flight t p)) := by
  have hbound (z) : |forcing q b L F.value z| ≤ HotApplication.realBound q*R^2+L*R := by
    have h := HotRepresentative.source_bounds hq₂ hb hR hloss
      (GaussianLocal.measurable_state F.measurable_value)
      (fun p => F.value_bounds (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
    change 0 ≤ forcing q b L F.value z ∧ forcing q b L F.value z ≤ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hmild : ∀ t ∈ Icc 0 T, (fun p => F.value (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀
        (forcing q b L F.value) (t,p)) := by
    intro t ht
    refine (F.mild t ⟨ht.1,ht.2.trans hTU⟩).trans (ae_of_all _ (fun p => ?_))
    exact PositiveIntegral.value_eq_at_time ⟨ht.1,ht.2.trans hTU⟩ ht.2 L f₀
      (fun _ _ _ => rfl) p
  have hloc := PositiveIntegral.localized_characteristic hT hf₀ F.measurable_value
    (measurable_forcing F.measurable_value q b L) hbound hmild χ χ' hχ hχ' hdχ
  have hgood : ∀ᵐ p ∂FlightMeasure.phaseVolume, p.2 ∈ HotRepresentative.good q := by
    apply (Measure.ae_prod_iff_ae_ae ((HotRepresentative.measurableSet_good q).preimage measurable_snd)).mpr
    exact ae_of_all _ (fun _ => HotRepresentative.ae_good hcarleman hq₁ hq₂)
  filter_upwards [hloc,hgood] with p hp hpg
  have hmuleq := congrArg (fun r : ℝ => H q p.2*r) hp
  rw [mul_add,← intervalIntegral.integral_const_mul] at hmuleq
  calc
    _ = H q p.2*(χ p T*F.value (T,JetBarrier.flight T p)) := by
      dsimp [density,JetBarrier.flight]
      ring
    _ = _ := hmuleq
    _ = _ := by
      congr 1
      · ring
      · apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        have hsrc := source_eq (b := b) (L := L) F.value hpg t
        rw [← hsrc]
        dsimp [density,JetBarrier.flight]
        ring

end BoltzmannNonuniqueness.PhysicalLocalization

end

end

section

/-! # The undamped characteristic equation of the actual physical density -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PhysicalLocalization

theorem characteristic (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 ≤ T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      density q F.value (T,JetBarrier.flight T p) = H q p.2*f₀ p +
        ∫ t in 0..T, source b q F.value (t,JetBarrier.flight t p) := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    convert (hasDerivAt_neg t).exp using 1
    ring
  have he := localized hcarleman F hq₁ hq₂ hb hR hT hTU hloss hf₀
    (fun _ t => Real.exp (-t)) (fun _ t => -Real.exp (-t))
    (fun _ => (Real.continuous_exp.comp continuous_neg).continuousOn)
    (fun _ => (Real.continuous_exp.comp continuous_neg).neg.continuousOn)
    (fun _ t _ => hd t)
  filter_upwards [he] with p hp
  have hi : (∫ t in 0..T, Real.exp (-(T-t)) *
      (Real.exp (-t)*source b q F.value (t,JetBarrier.flight t p) +
        (-Real.exp (-t)+Real.exp (-t))*density q F.value (t,JetBarrier.flight t p))) =
      Real.exp (-T)*(∫ t in 0..T, source b q F.value (t,JetBarrier.flight t p)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [neg_add_cancel,zero_mul,add_zero,← mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [hi] at hp
  simp only [neg_zero,Real.exp_zero,mul_one] at hp
  apply (mul_left_cancel₀ (Real.exp_ne_zero (-T)))
  calc
    _ = Real.exp (-T)*(H q p.2*f₀ p) +
        Real.exp (-T)*(∫ t in 0..T, source b q F.value (t,JetBarrier.flight t p)) := by
      simpa only [mul_assoc] using hp
    _ = _ := (mul_add _ _ _).symm

end BoltzmannNonuniqueness.PhysicalLocalization

end

end

end OAI
