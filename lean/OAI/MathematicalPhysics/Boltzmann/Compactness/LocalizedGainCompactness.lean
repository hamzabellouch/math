import OAI.MathematicalPhysics.Boltzmann.Branching.GainSmoothingError
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongCompactPairTests

namespace OAI

/-! # Removing velocity smoothing from entropy-controlled localized gains -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem velocitySmooth_error_eLpNorm_le {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) {ε : ℝ}
    (he : (∫ p, |velocitySmooth χ F p-F p| ∂μ.prod volume) ≤ ε) :
    eLpNorm (velocitySmooth χ F-F) 1 (μ.prod volume) ≤ ENNReal.ofReal ε := by
  have hi := (velocitySmooth_integrable hχ hF).sub hF
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hi]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using he)

theorem localizedGain_strong_of_smoothing
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) (μ.prod volume))
    (η : C(Velocity,ℝ)) (hη : HasCompactSupport η)
    {ν : Measure (X × Velocity)} (hν : ν ≤ μ.prod volume)
    (hc : ∀ χ : C(Velocity,ℝ), HasCompactSupport χ →
      Tendsto (fun n => eLpNorm
        (velocitySmooth χ (localizedPhysicalGain η (f n))-
          velocitySmooth χ (localizedPhysicalGain η g)) 1 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm
      (localizedPhysicalGain η (f n)-localizedPhysicalGain η g) 1 ν) atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hε j : 0 < ε j := by dsimp [ε]; positivity
  have hchoice j : ∃ χ : C(Velocity,ℝ), HasCompactSupport χ ∧ Integrable χ ∧
      (∀ n, (∫ p, |velocitySmooth χ (localizedPhysicalGain η (f n)) p-
        localizedPhysicalGain η (f n) p| ∂μ.prod volume) ≤ ε j) ∧
      (∫ p, |velocitySmooth χ (localizedPhysicalGain η g) p-
        localizedPhysicalGain η g p| ∂μ.prod volume) ≤ ε j := by
    obtain ⟨d,hd,hds⟩ := localizedGain_uniform_smoothing hfm hf hi hb η hη (ε j) (hε j)
    obtain ⟨e,he,hes⟩ := localizedGain_uniform_smoothing
      (fun _ : ℕ => hgm) (fun _ => hg) (fun _ => hgi)
      (fun _ => le_refl (∫ p, entropyGauge g p ∂μ.prod volume)) η hη (ε j) (hε j)
    obtain ⟨χ,hχc,hχi,hχ0,hχm,hχs⟩ := exists_velocity_mollifier (lt_min hd he)
    refine ⟨χ,hχc,hχi,?_,?_⟩
    · exact hds χ hχi hχ0 hχm (fun a ha => (hχs a ha).trans_le (min_le_left _ _))
    · exact hes χ hχi hχ0 hχm (fun a ha => (hχs a ha).trans_le (min_le_right _ _)) 0
  choose χ hχc hχi hχf hχg using hchoice
  have hδ : Tendsto (fun j => ENNReal.ofReal (ε j)) atTop (𝓝 0) := by
    have he : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.tendsto 0 |>.comp he
  have hFi n : Integrable (localizedPhysicalGain η (f n)) (μ.prod volume) := by
    apply localizedPhysicalGain_integrable η hη (hfm n)
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  have hGi : Integrable (localizedPhysicalGain η g) (μ.prod volume) := by
    apply localizedPhysicalGain_integrable η hη hgm
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable hgm hg hgi
  apply strongL1_of_two_sided_approximations hδ
    (u := fun j n => velocitySmooth (χ j) (localizedPhysicalGain η (f n)))
    (v := fun j => velocitySmooth (χ j) (localizedPhysicalGain η g))
  · intro j n
    rw [eLpNorm_sub_comm]
    exact (eLpNorm_mono_measure _ hν).trans
      (velocitySmooth_error_eLpNorm_le (hχi j) (hFi n) (hχf j n))
  · intro j
    exact (eLpNorm_mono_measure _ hν).trans
      (velocitySmooth_error_eLpNorm_le (hχi j) hGi (hχg j))
  · exact fun j => hc (χ j) (hχc j)

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end OAI
