import OAI.MathematicalPhysics.Boltzmann.Approximation.ResolventAverageBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.MeasurableResolvent
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMomentEntropy

namespace OAI

section

/-! # Integrating a uniform entropy budget over a bounded time window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def spacetimeEntropy (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  F z*(1+‖z.2.2‖^2+|Real.log (F z)|)

theorem spacetimeEntropy_measurable {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (spacetimeEntropy F) :=
  hF.mul ((measurable_const.add (measurable_snd.snd.norm.pow_const 2)).add hF.log.abs)

theorem spacetimeEntropy_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {F : ℝ × Phase → ℝ} {C : ℝ} (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : ∀ t, Integrable (entropyMoment (fun p => F (t,p))))
    (hb : ∀ t, (∫ p, entropyMoment (fun p => F (t,p)) p) ≤ C) :
    Integrable (spacetimeEntropy F) (μ.prod volume) := by
  have hm := spacetimeEntropy_measurable hFm
  have hn (z : ℝ × Phase) : 0 ≤ spacetimeEntropy F z := mul_nonneg (hF z) (by positivity)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall hi
  · have hnorm : (fun t => ∫ p, ‖spacetimeEntropy F (t,p)‖) =
        (fun t => ∫ p, spacetimeEntropy F (t,p)) := by
      funext t
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => Real.norm_of_nonneg (hn (t,p)))
    rw [hnorm]
    apply (integrable_const C).mono' hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (integral_nonneg (fun p => hn (t,p)))]
    exact hb t

theorem spacetimeEntropy_integral_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    {F : ℝ × Phase → ℝ} {C : ℝ} (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : ∀ t, Integrable (entropyMoment (fun p => F (t,p))))
    (hb : ∀ t, (∫ p, entropyMoment (fun p => F (t,p)) p) ≤ C) :
    (∫ z, spacetimeEntropy F z ∂μ.prod volume) ≤ μ.real univ*C := by
  have hi' := spacetimeEntropy_integrable (μ := μ) hFm hF hi hb
  rw [integral_prod _ hi']
  exact (integral_mono hi'.integral_prod_left (integrable_const C) hb).trans_eq (integral_const C)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Resolvent representation on spacetime, including actual velocity averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem spacetime_resolvent (hcarleman : Published.GPV2009CarlemanInput)
    {q b L U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) :
    (fun z => χ z*density q F.value z) =ᵐ[
      ((volume.restrict (Icc 0 U)).prod (volume : Measure Velocity)).prod volume]
      Published.transportResolvent (localizedSource U χ (density q F.value) (source b q F.value)) := by
  let f := density q F.value
  let r := localizedSource U χ f (source b q F.value)
  have hfm : Measurable f := density_measurable F.measurable_value q
  have hQm : Measurable (source b q F.value) := by
    rw [source_eq_collision]
    exact CollisionCompactness.collisionSource_measurable hfm b
  have hrm : Measurable r := localizedSource_measurable hχ hfm hQm
  have hm : MeasurableSet {z : ℝ × (Velocity × Velocity) |
      χ ((z.1,z.2.1),z.2.2)*f ((z.1,z.2.1),z.2.2) =
        Published.transportResolvent r ((z.1,z.2.1),z.2.2)} := by
    exact (measurableSet_eq_fun (hχ.continuous.measurable.mul hfm)
      (Published.transportResolvent_measurable hrm)).preimage (by fun_prop)
  have ht : ∀ᵐ t ∂volume.restrict (Icc 0 U), ∀ᵐ p ∂(volume : Measure (Velocity × Velocity)),
      χ ((t,p.1),p.2)*f ((t,p.1),p.2) = Published.transportResolvent r ((t,p.1),p.2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact resolvent_representation hcarleman F hq₁ hq₂ hb hR ht.1 ht.2 hloss hf₀ hχ hzero
  have hfull := (Measure.ae_prod_iff_ae_ae hm).mpr ht
  exact (measurePreserving_prodAssoc (volume.restrict (Icc 0 U))
    (volume : Measure Velocity) (volume : Measure Velocity)).quasiMeasurePreserving.ae hfull

theorem velocity_averages_resolvent (hcarleman : Published.GPV2009CarlemanInput)
    {q b L U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : WeightedLocalControl.PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (hf₀ : Measurable f₀)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0)
    (ψ : Velocity → ℝ) :
    (fun z : Published.SpaceTime => ∫ v, ψ v*(χ (z,v)*density q F.value (z,v))) =ᵐ[
      (volume.restrict (Icc 0 U)).prod (volume : Measure Velocity)]
      Published.resolventAverage (localizedSource U χ (density q F.value) (source b q F.value)) ψ := by
  have he := Measure.ae_ae_of_ae_prod
    (spacetime_resolvent hcarleman F hq₁ hq₂ hb hR hloss hf₀ hχ hzero)
  filter_upwards [he] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with v hv
  rw [hv]

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Relative entropy and the absolute entropy moment in spacetime -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def spacetimeRelativeEntropy (F : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  scalarRelativeEntropy (maxwellian z.2.2) (F z)

theorem spacetimeRelativeEntropy_measurable {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (spacetimeRelativeEntropy F) :=
  scalarRelativeEntropy_measurable (by unfold maxwellian; fun_prop) hF

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {F : ℝ × Phase → ℝ}

omit [IsFiniteMeasure μ] in
theorem density_integrable_of_spacetimeEntropy (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : Integrable (spacetimeEntropy F) (μ.prod volume)) :
    Integrable F (μ.prod volume) := by
  apply hi.mono' hFm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_of_nonneg (hF z)]
    have h : 1 ≤ 1+‖z.2.2‖^2+|Real.log (F z)| := by
      nlinarith [sq_nonneg ‖z.2.2‖,abs_nonneg (Real.log (F z))]
    simpa only [spacetimeEntropy,mul_one] using mul_le_mul_of_nonneg_left h (hF z))

theorem relativeEntropy_integrable_of_spacetimeEntropy
    (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : Integrable (spacetimeEntropy F) (μ.prod volume)) :
    Integrable (spacetimeRelativeEntropy F) (μ.prod volume) := by
  have hM := integrable_maxwellian_phase.comp_snd μ
  apply ((hi.const_mul initialEntropyCoefficient).add hM).mono'
    (spacetimeRelativeEntropy_measurable hFm).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    dsimp only [spacetimeRelativeEntropy,Pi.add_apply]
    rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos _) (hF z))]
    exact relativeEntropy_density_bound (fun p => hF (z.1,p)) z.2)

theorem spacetimeEntropy_integrable_of_relativeEntropy
    (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : Integrable (spacetimeRelativeEntropy F) (μ.prod volume)) :
    Integrable (spacetimeEntropy F) (μ.prod volume) := by
  have hG := (entropyGaussian_integrable.comp_snd (volume : Measure Position)).comp_snd μ
  have hM := integrable_maxwellian_phase.comp_snd μ
  have hmajor := ((hi.const_mul (1+4*entropyMomentCoefficient)).add
    (hG.const_mul (4*entropyMomentCoefficient))).add hM
  apply hmajor.mono' (spacetimeEntropy_measurable hFm).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_of_nonneg (show 0 ≤ spacetimeEntropy F z from
      mul_nonneg (hF z) (by positivity))]
    exact entropyMoment_control (f := fun p => F (z.1,p)) (z := z.2) (hF z))

theorem spacetimeRelativeEntropy_integral_le
    (hi : Integrable (spacetimeRelativeEntropy F) (μ.prod volume)) {C : ℝ}
    (hb : ∀ t, relativeEntropy (fun p => F (t,p)) ≤ C) :
    (∫ z, spacetimeRelativeEntropy F z ∂μ.prod volume) ≤ μ.real univ*C := by
  rw [integral_prod _ hi]
  have he (t : ℝ) : (∫ p, spacetimeRelativeEntropy F (t,p)) =
      relativeEntropy (fun p => F (t,p)) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  exact (integral_mono hi.integral_prod_left (integrable_const C)
    (fun t => (he t).trans_le (hb t))).trans_eq (integral_const C)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
