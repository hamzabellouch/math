import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability

namespace OAI

/-! # The physical frequency is globally integrable with Maxwellian weight -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem maxwellian_kineticFrequency_integrable {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (linearMoment f) (μ.prod volume)) :
    Integrable (fun p => maxwellian p.2*kineticFrequency f p) (μ.prod volume) := by
  have hwi : Integrable (fun v : Velocity => (1+‖v‖)*maxwellian v) := by
    convert integrable_maxwellian.add integrable_maxwellian_firstMoment using 1
    funext v
    dsimp only [Pi.add_apply]
    ring
  have hmajor := (hi.integral_prod_left.mul_prod hwi).const_mul (2*Real.pi)
  have hMm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  apply hmajor.mono' (hMm.mul (kineticFrequency_measurable hfm)).aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ)
    (ν := (volume : Measure Velocity))).ae hi.prod_right_ae] with p hp
  have hb w : ‖‖p.2-w‖*f (p.1,w)‖ ≤ (1+‖p.2‖)*linearMoment f (p.1,w) := by
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hf _))]
    apply le_trans (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (hf _))
    have hc : ‖p.2‖+‖w‖ ≤ (1+‖p.2‖)*(1+‖w‖) := by nlinarith [norm_nonneg w,norm_nonneg p.2]
    simpa only [linearMoment,mul_assoc] using mul_le_mul_of_nonneg_right hc (hf (p.1,w))
  have hh := norm_integral_le_of_norm_le (hp.const_mul (1+‖p.2‖)) (ae_of_all _ hb)
  rw [integral_const_mul] at hh
  have hν : kineticFrequency f p ≤ 2*Real.pi*((1+‖p.2‖)*(∫ w, linearMoment f (p.1,w))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hh (by positivity))
    simpa only [kineticFrequency, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (le_abs_self (∫ w, ‖p.2-w‖*f (p.1,w)))
        (show 0 ≤ 2*Real.pi by positivity)
  change ‖maxwellian p.2*kineticFrequency f p‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (maxwellian_pos p.2).le (kineticFrequency_nonneg hf p))]
  calc
    _ ≤ maxwellian p.2*(2*Real.pi*((1+‖p.2‖)*(∫ w, linearMoment f (p.1,w)))) :=
      mul_le_mul_of_nonneg_left hν (maxwellian_pos p.2).le
    _ = _ := by ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
