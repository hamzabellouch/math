import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedMeshStep
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityFourierMultiplier
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityWeight
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalFrequencyWindow

namespace OAI

section

/-! # The actual velocity average satisfies the localized spectral estimate -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

theorem fourier_average_multiplier {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (k : FourierSpace) :
    𝓕 (velocityLineAverage r) k = ∫ v,
      complexVelocityMultiplier 1 (physicalFourierFrequency k) v * velocityFourier r (v,k) := by
  rw [fourier_velocityLineAverage hr]
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    dsimp only
    rw [physicalFourierMultiplier]
    rfl)

theorem average_spectral_estimate {r : Velocity × FourierSpace → ℂ}
    (hr : Measurable r) (h₁ : Integrable r) (h₂ : MemLp r 2 volume) {R : ℝ}
    (hs : ∀ᵐ p ∂(volume : Measure (Velocity × FourierSpace)), R < ‖p.1‖ → r p = 0) :
    ∀ᵐ k ∂(volume : Measure FourierSpace),
      ‖𝓕 (velocityLineAverage r) k‖^2 ≤
        velocityMultiplierMass R 1 (physicalFourierFrequency k) *
          ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 := by
  have hi := velocityFourier_integrable_sq hr h₁ h₂
  have hsupport := velocityFourier_support hs
  filter_upwards [hi.prod_left_ae] with k hk
  have hmem : MemLp (fun v => velocityFourier r (v,k)) 2
      (volume.restrict (Metric.closedBall (0 : Velocity) R)) := by
    apply (memLp_two_iff_integrable_sq_norm
      (((velocityFourier_measurable hr).comp measurable_prodMk_right).aestronglyMeasurable.restrict)).mpr
    exact hk.restrict
  have he : (∫ v in Metric.closedBall (0 : Velocity) R,
        complexVelocityMultiplier 1 (physicalFourierFrequency k) v * velocityFourier r (v,k)) =
      ∫ v, complexVelocityMultiplier 1 (physicalFourierFrequency k) v * velocityFourier r (v,k) := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupport] with v hv
    intro hnot
    have hR : R < ‖v‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hnot
    rw [hv hR k,mul_zero]
  rw [fourier_average_multiplier h₁,← he]
  apply (velocity_spectral_integral_bound R (physicalFourierFrequency k) hmem).trans
  apply mul_le_mul_of_nonneg_left _ (velocityMultiplierMass_nonneg _ _ _)
  exact setIntegral_le_integral hk (ae_of_all _ (fun v => sq_nonneg _))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform Fourier tails for the actual bounded velocity averages -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] velocityFourier velocityLineAverage physicalFourierFrequency

theorem average_fourier_tail {R ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ (r : Velocity × FourierSpace → ℂ),
      Measurable r → Integrable r → MemLp r 2 volume →
      MemLp (velocityLineAverage r) 2 volume →
      (∀ᵐ p ∂(volume : Measure (Velocity × FourierSpace)), R < ‖p.1‖ → r p = 0) →
      (∫ k in {k : FourierSpace | (N:ℝ) ≤ ‖physicalFourierFrequency k‖},
        ‖𝓕 (velocityLineAverage r) k‖^2) ≤ ε * ∫ p, ‖r p‖^2 := by
  obtain ⟨N,hN,hbound⟩ := velocityMultiplierMass_high_frequency R hε
  refine ⟨N,hN,?_⟩
  intro r hr h₁ h₂ ha hs
  have hF := fourier_integral_memLp (velocityLineAverage_integrable h₁) ha
  have hFi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hpi := velocityFourier_integrable_sq hr h₁ h₂
  have hei : Integrable (fun k => ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2) :=
    hpi.integral_prod_right
  let S : Set FourierSpace := {k | (N:ℝ) ≤ ‖physicalFourierFrequency k‖}
  have hm : MeasurableSet S := by
    apply measurableSet_le measurable_const
    unfold physicalFourierFrequency
    fun_prop
  have hp : ∀ᵐ k ∂volume.restrict S,
      ‖𝓕 (velocityLineAverage r) k‖^2 ≤
        ε * ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 := by
    filter_upwards [ae_restrict_of_ae (average_spectral_estimate hr h₁ h₂ hs),
      ae_restrict_mem hm] with k hk hks
    exact hk.trans (mul_le_mul_of_nonneg_right (hbound _ hks).le (integral_nonneg (fun v => sq_nonneg _)))
  calc
    _ ≤ ∫ k in S, ε * ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 :=
      integral_mono_ae hFi.restrict (hei.const_mul ε).restrict hp
    _ ≤ ∫ k, ε * ∫ v : Velocity, ‖velocityFourier r (v,k)‖^2 :=
      setIntegral_le_integral (hei.const_mul ε)
        (ae_of_all _ (fun k => mul_nonneg hε.le (integral_nonneg (fun v => sq_nonneg _))))
    _ = ε * ∫ p, ‖r p‖^2 := by
      rw [integral_const_mul,← integral_prod_symm _ hpi]
      change ε*(∫ p, ‖velocityFourier r p‖^2) = _
      rw [velocityFourier_energy hr h₁ h₂]

end BoltzmannNonuniqueness.Published

end

end

end OAI
