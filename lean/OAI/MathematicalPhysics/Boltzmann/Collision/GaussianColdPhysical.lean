import OAI.MathematicalPhysics.Boltzmann.Jets.ColdGaussianFamily
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianLocalExistence
import OAI.MathematicalPhysics.Boltzmann.Jets.JetPeriodicDatum

namespace OAI

/-! # The positive cold iteration in the original collision variables -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.GaussianLocal

theorem physical_coldForcing (β b L : ℝ) (F c : ℝ × JetPrototype.Phase → ℝ)
    (z : ℝ × JetPrototype.Phase) :
    JetGaussianMoments.kernel β z.2.2 * coldForcing β b L F c z =
      CollisionCutoff.gain b (fun v => physical β c (z.1, (z.2.1, v))) z.2.2 +
      (L - CollisionCutoff.frequency b (fun v => physical β F (z.1, (z.2.1, v))) z.2.2) *
        physical β c z := by
  unfold coldForcing GaussianCutoff.coldSource
  have he := GaussianCutoff.gain_eq_actual β b (state c) ((z.1, z.2.1), z.2.2)
  dsimp only at he
  rw [mul_add, he]
  simp only [state, physical, GaussianCutoff.frequency, KineticCollisionNullSets.frequency]
  ring

theorem physical_value_along {β b L T t : ℝ} (ht : t ∈ Icc 0 T)
    (F c : ℝ × JetPrototype.Phase → ℝ) (c₀ : JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    physical β (PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing β b L F c))
        (t, JetBarrier.flight t p) =
      Real.exp (-L*t) * (JetGaussianMoments.kernel β p.2 * c₀ p) +
      ∫ r in 0..t, Real.exp (-L*(t-r)) *
        (CollisionCutoff.gain b
          (fun v => physical β c (r, ((JetBarrier.flight r p).1, v))) p.2 +
          (L - CollisionCutoff.frequency b
            (fun v => physical β F (r, ((JetBarrier.flight r p).1, v))) p.2) *
            physical β c (r, JetBarrier.flight r p)) := by
  unfold physical PositiveIntegral.value
  rw [time_eq ht]
  simp only [JetFreeTransport.flight_add, neg_add_cancel, JetFreeTransport.flight_zero,
    sub_add_cancel]
  change JetGaussianMoments.kernel β p.2 * _ = _
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  · ring
  · apply intervalIntegral.integral_congr
    intro r _
    have he := physical_coldForcing β b L F c (r, JetBarrier.flight r p)
    change JetGaussianMoments.kernel β p.2 * _ = _ at he
    dsimp only at he ⊢
    rw [mul_left_comm, he]
    rfl


theorem physical_cold_integrable {β b L T R t : ℝ} (hβ : 0 < β) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : GaussianCutoff.lossConstant β b * R ≤ L)
    {F c : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (ht : t ∈ Icc 0 T) (p : JetPrototype.Phase) :
    IntervalIntegrable (fun r => Real.exp (-L*(t-r)) *
      (CollisionCutoff.gain b (fun v => physical β c (r, ((JetBarrier.flight r p).1, v))) p.2 +
        (L - CollisionCutoff.frequency b
          (fun v => physical β F (r, ((JetBarrier.flight r p).1, v))) p.2) *
          physical β c (r, JetBarrier.flight r p))) volume 0 t := by
  have hs (z) : |coldForcing β b L F c z| ≤
      GaussianCutoff.gainConstant β b * R ^ 2 + L*R := by
    have h := GaussianCutoff.coldSource_bounds hβ hb hR hloss
      (fun q => hF (q.1.1, (q.1.2, q.2))) (fun q => hc (q.1.1, (q.1.2, q.2)))
      ((z.1, z.2.1), z.2.2)
    change 0 ≤ coldForcing β b L F c z ∧ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hi := (PositiveIntegral.damped_integrable hT hL measurable_flight
    (measurable_coldForcing hFm hcm β b L) hs (t, JetBarrier.flight t p)).const_mul
      (JetGaussianMoments.kernel β p.2)
  rw [time_eq ht] at hi
  simp only [JetFreeTransport.flight_add, sub_add_cancel] at hi
  have hi' : IntervalIntegrable (fun r => JetGaussianMoments.kernel β p.2 *
      (Real.exp (-L*(t-r)) * coldForcing β b L F c (r, JetBarrier.flight r p))) volume 0 t := hi
  apply hi'.congr_ae
  filter_upwards [] with r
  have he := physical_coldForcing β b L F c (r, JetBarrier.flight r p)
  change JetGaussianMoments.kernel β p.2 * _ = _ at he
  rw [mul_left_comm, he]
  rfl

end BoltzmannNonuniqueness.GaussianLocal

end

end OAI
