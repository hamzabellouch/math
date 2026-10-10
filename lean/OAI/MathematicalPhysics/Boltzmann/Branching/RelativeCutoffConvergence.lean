import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairBoundedTruncation

namespace OAI

section

/-! # The cutoff relative-entropy production about the Maxwellian -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_log_relative (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p => Real.log (f p/maxwellian p.2)) z =
      collisionJump (fun p => Real.log (f p)) z := by
  have hl (p : X × Velocity) : Real.log (f p/maxwellian p.2) =
      Real.log (f p)-Real.log (maxwellian p.2) :=
    Real.log_div (hf p).ne' (maxwellian_pos p.2).ne'
  have he : collisionJump (fun p => Real.log (f p/maxwellian p.2)) z =
      collisionJump (fun p => Real.log (f p)) z-
        collisionJump (fun p : X × Velocity => Real.log (maxwellian p.2)) z := by
    simp only [collisionJump,hl]
    ring
  rw [he,collisionJump_log_maxwellian,sub_zero]

omit [MeasurableSpace X] in
theorem relative_entropy_production_nonneg (b : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
      (truncatedPostRate b f z-truncatedPreRate b f z) := by
  rw [collisionJump_log_relative f hf]
  exact entropy_production_nonneg b f hf z

theorem cutoff_relative_entropy_nonpositive {μ : Measure X} [SFinite μ] (b : ℝ)
    (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (hpre : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)*
      truncatedPreRate b f z) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)*
      truncatedPostRate b f z) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ p, Real.log (f p/maxwellian p.2)*KineticCollisionNullSets.gain b f p ∂μ.prod volume)-
      (∫ p, Real.log (f p/maxwellian p.2)*cutoffLossDensity b f p ∂μ.prod volume) ≤ 0 := by
  have hp := (collision_test_marginal (truncatedPostRate b f)
    (fun p => Real.log (f p/maxwellian p.2)) hpost).2
  have hl := (collision_test_marginal (truncatedPreRate b f)
    (fun p => Real.log (f p/maxwellian p.2)) hpre).2
  simp only [← cutoffGain_eq_marginal] at hp
  simp only [← cutoffLoss_eq_marginal] at hl
  rw [hp,hl,cutoff_production_identity b f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost]
  have hn : 0 ≤ ∫ z, collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
      (truncatedPostRate b f z-truncatedPreRate b f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
    integral_nonneg (relative_entropy_production_nonneg b f hf)
  linarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Moving hard-sphere velocity cutoffs disappear in the mixed weak limit -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem relative_cutoff_difference_tendsto
    {μ : ℕ → Measure (X × (Velocity × Velocity))} {M : ℝ} (hM : 0 ≤ M)
    (hμ : ∀ᶠ n in atTop,
      (∫⁻ p, ENNReal.ofReal (weight p.2.1*weight p.2.2) ∂μ n) ≤ ENNReal.ofReal M)
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop)
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    {f : Velocity × Velocity → ℝ} (hfm : Measurable f)
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ p, |f p| ≤ L*(1+‖p.1‖+‖p.2‖)) :
    Tendsto (fun n => (∫ p, θ p.1*relativeCutoff (b n) f p.2 ∂μ n)-
      (∫ p, θ p.1*f p.2 ∂μ n)) atTop (𝓝 0) := by
  have hfg (p) : |f p| ≤ (3*L)*(weight p.1*weight p.2) :=
    (hf p).trans ((mul_le_mul_of_nonneg_left (pair_weight_le p.1 p.2) hL).trans_eq (by ring))
  have hlim : Tendsto (fun n => |B| *(12*L/b n)*M) atTop (𝓝 0) := by
    simpa using ((hb.const_div_atTop (12*L)).const_mul |B|).mul_const M
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hμ,hb.eventually (eventually_ge_atTop 2)] with n hn hbn
  have he := Compactness.weighted_gaussian_error (μ n) hM hn hθ hB hfm
    (relativeCutoff_measurable hfm (b n))
    (div_nonneg (mul_nonneg (by norm_num) hL) (by linarith : 0 ≤ b n)) hfg
    (relativeCutoff_gaussian_error hbn hL hf)
  simpa only [Real.norm_eq_abs] using he

theorem relative_cutoff_integral_tendsto
    {μ : ℕ → Measure (X × (Velocity × Velocity))} {M : ℝ} (hM : 0 ≤ M)
    (hμ : ∀ᶠ n in atTop,
      (∫⁻ p, ENNReal.ofReal (weight p.2.1*weight p.2.2) ∂μ n) ≤ ENNReal.ofReal M)
    {b : ℕ → ℝ} (hb : Tendsto b atTop atTop)
    {θ : X → ℝ} (hθ : Measurable θ) {B : ℝ} (hB : ∀ x, |θ x| ≤ B)
    {f : Velocity × Velocity → ℝ} (hfm : Measurable f)
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ p, |f p| ≤ L*(1+‖p.1‖+‖p.2‖))
    {c : ℝ} (hc : Tendsto (fun n => ∫ p, θ p.1*f p.2 ∂μ n) atTop (𝓝 c)) :
    Tendsto (fun n => ∫ p, θ p.1*relativeCutoff (b n) f p.2 ∂μ n) atTop (𝓝 c) := by
  have ht := (relative_cutoff_difference_tendsto hM hμ hb hθ hB hfm hL hf).add hc
  simpa only [sub_add_cancel,zero_add] using ht

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
