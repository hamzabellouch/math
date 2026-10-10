import OAI.MathematicalPhysics.Boltzmann.Branching.VaryingBoundedMultiplier
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # A vanishing local L1 error vanishes against every bounded measurable test -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_tendsto_zero_of_L1 {f : ℕ → X → ℝ}
    (h : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 0) := by
  have hi : ∀ᶠ n in atTop, Integrable (f n) μ :=
    (h.eventually (eventually_lt_nhds (show (0 : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top))).mono
      (fun _ hn => memLp_one_iff_integrable.mp hn)
  simpa only [sub_zero,integral_zero] using
    tendsto_integral_of_L1' (fun _ : X => (0:ℝ)) hi (by simpa only [Pi.sub_def,sub_zero] using h)

theorem bounded_test_integral_tendsto_zero {f : ℕ → X → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (f n) μ)
    (h : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0))
    {ψ : X → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : 0 ≤ C)
    (hψC : ∀ x, |ψ x| ≤ C) :
    Tendsto (fun n => ∫ x, ψ x*f n x ∂μ) atTop (𝓝 0) := by
  apply integral_tendsto_zero_of_L1
  exact tendsto_L1_bounded_mul_zero hm (fun _ => hψ.aestronglyMeasurable) h hC
    (Eventually.of_forall (fun _ => ae_of_all _ hψC))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Vanishing of scaled cutoff collision terms from positive weak limits -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem vanishing_cutoff_collision
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} {g h : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hfn : ∀ n z, 0 ≤ f n z)
    (hpair : ∀ᶠ n in atTop, Integrable (pairDensity (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))))
    (hg : Published.WeakL1Converges (μ.prod volume) (fun n => gainDensity (f n)) g)
    (hl : Published.WeakL1Converges (μ.prod volume) (fun n => lossDensity (f n)) h)
    (b : ℕ → ℝ) {c : ℕ → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun p => c n*collisionSource (b n) (f n) p)
      1 (μ.prod volume)) atTop (𝓝 0) := by
  have hi : ∀ᶠ n in atTop, Integrable (gainDensity (f n)) (μ.prod volume) ∧
      Integrable (lossDensity (f n)) (μ.prod volume) :=
    hpair.mono (fun n hn => gainLoss_integrable (hfm n) (hfn n) hn)
  have hgain := hg.vanishing_scalar (hi.mono (fun _ hn => hn.1))
    (fun n => ae_of_all _ (gainDensity_nonneg (hfn n))) hc
  have hloss := hl.vanishing_scalar (hi.mono (fun _ hn => hn.2))
    (fun n => ae_of_all _ (lossDensity_nonneg (hfn n))) hc
  have hcg : Tendsto (fun n => eLpNorm
      (fun p => c n*KineticCollisionNullSets.gain (b n) (f n) p) 1 (μ.prod volume))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgain
      (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
    filter_upwards [hpair] with n hn
    apply eLpNorm_mono_ae
      ((KineticCollisionNullSets.measurable_gain (hfm n) (b n)).const_mul _).aestronglyMeasurable
    filter_upwards [cutoff_gainLoss_le (hfm n) (hfn n) hn (b n)] with p hp
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_mul,
      abs_of_nonneg (cutoffGainDensity_nonneg (hfn n) _ _),
      abs_of_nonneg (gainDensity_nonneg (hfn n) _)]
    exact mul_le_mul_of_nonneg_left hp.1 (abs_nonneg _)
  have hcl : Tendsto (fun n => eLpNorm
      (fun p => c n*cutoffLossDensity (b n) (f n) p) 1 (μ.prod volume))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hloss
      (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
    filter_upwards [hpair] with n hn
    apply eLpNorm_mono_ae
      ((cutoffLossDensity_measurable (hfm n) (b n)).const_mul _).aestronglyMeasurable
    filter_upwards [cutoff_gainLoss_le (hfm n) (hfn n) hn (b n)] with p hp
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_mul,
      abs_of_nonneg (cutoffLossDensity_nonneg (hfn n) _ _),
      abs_of_nonneg (lossDensity_nonneg (hfn n) _)]
    exact mul_le_mul_of_nonneg_left hp.2 (abs_nonneg _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_add] using hcg.add hcl)
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [hpair] with n hn
  have he : (fun p => c n*collisionSource (b n) (f n) p) =ᵐ[μ.prod volume]
      fun p => c n*KineticCollisionNullSets.gain (b n) (f n) p-
        c n*cutoffLossDensity (b n) (f n) p := by
    filter_upwards [cutoff_loss_ae_eq_frequency (hfm n) (hfn n) hn (b n)] with p hp
    unfold collisionSource
    rw [hp,mul_sub]
  rw [eLpNorm_congr_ae he]
  exact eLpNorm_sub_le (by norm_num)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
