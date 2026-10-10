import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialIntegralUniform
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressurePrimitive
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialClampedPhase

namespace OAI

/-! Uniform convergence of the phase and its actual first derivative. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

noncomputable def radialPhaseSpeed (c : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
  (radialVelocity c A r-r/2)/2

theorem radial_phase_speed_continuousOn (c R : ℝ) (A : ℝ → ℝ) (hR : 0 ≤ R)
    (hA : Continuous A) (hAz : ∀ r ∈ Icc 0 R, A r ≠ 0) :
    ContinuousOn (radialPhaseSpeed c A) (Icc 0 R) := by
  have hc := continuous_radialVelocity c (radialClampedAmplitude R A)
    (radialClampedAmplitude_continuous R A hA)
    (fun r => hAz _ (radialClamp_mem R r hR))
  apply ((hc.sub (continuous_id.div_const 2)).div_const 2).continuousOn.congr
  intro r hr
  dsimp [radialPhaseSpeed]
  rw [radialVelocity_clamped_eq c R A r hr]

theorem radial_phase_speed_uniform (R : ℝ) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : ∀ n, c n ∈ Icc (599/100 : ℝ) 6) (hcT : Tendsto c atTop (𝓝 c₀))
    (H : ℕ → ℝ → ℝ) (A : ℝ → ℝ) (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hHI : ∀ n r, r ∈ Icc 0 R → H n r ∈ Icc (999/1000 : ℝ) 1)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hT : TendstoUniformlyOn H A atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n => radialPhaseSpeed (c n) (H n))
      (radialPhaseSpeed c₀ A) atTop (Icc 0 R) := by
  have hρ := radialVelocityRatio_uniform_convergence R c c₀ hc hcT H A hH hA hHI hAI hT
  have hid : TendstoUniformlyOn (fun _ : ℕ => fun r : ℝ => r) (fun r => r) atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hρc : ContinuousOn (radialVelocityRatio c₀ A) (Icc 0 R) := by
    exact ((continuous_const.mul (continuous_radialAverage (fun r => (A r)^2) (hA.pow 2))).continuousOn.div
      (hA.pow 2).continuousOn (fun r hr => pow_ne_zero 2
        (ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI r hr).1))))
  have hw := radial_uniform_product R _ _ _ _ hid hρ continuous_id.continuousOn hρc
  have hh : TendstoUniformlyOn (fun _ : ℕ => fun r : ℝ => r/2) (fun r => r/2) atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hhalf : TendstoUniformlyOn (fun _ : ℕ => fun _ : ℝ => (1/2 : ℝ)) (fun _ => (1/2 : ℝ))
      atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    exact fun ε hε => Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hv := radial_uniform_product R _ _ _ _ (hw.sub hh) hhalf
    ((continuous_id.continuousOn.mul hρc).sub (continuous_id.div_const 2).continuousOn) continuousOn_const
  change TendstoUniformlyOn
    (fun n r => (r*radialVelocityRatio (c n) (H n) r-r/2)/2)
    (fun r => (r*radialVelocityRatio c₀ A r-r/2)/2) atTop (Icc 0 R)
  simpa only [div_eq_mul_inv,one_mul,Pi.sub_apply] using hv

theorem radial_phase_clamped_uniform (R : ℝ) (hR : 0 ≤ R) (c : ℕ → ℝ) (c₀ : ℝ)
    (hc : ∀ n, c n ∈ Icc (599/100 : ℝ) 6) (hcT : Tendsto c atTop (𝓝 c₀))
    (H : ℕ → ℝ → ℝ) (A : ℝ → ℝ) (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hHI : ∀ n r, r ∈ Icc 0 R → H n r ∈ Icc (999/1000 : ℝ) 1)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hT : TendstoUniformlyOn H A atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n => radialPhase (c n) (radialClampedAmplitude R (H n)))
      (radialPhase c₀ (radialClampedAmplitude R A)) atTop (Icc 0 R) := by
  have hs := radial_phase_speed_uniform R c c₀ hc hcT H A hH hA hHI hAI hT
  have hi := radial_integral_uniform R hR _ _
    (fun n => radial_phase_speed_continuousOn (c n) R (H n) hR (hH n)
      (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hHI n r hr).1)))
    (radial_phase_speed_continuousOn c₀ R A hR hA
      (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI r hr).1))) hs
  have heq (d : ℝ) (B : ℝ → ℝ) (r : ℝ) (hr : r ∈ Icc 0 R) :
      (∫ t in (0 : ℝ)..r, radialPhaseSpeed d B t)=radialPhase d (radialClampedAmplitude R B) r := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc 0 r := uIcc_of_le hr.1 ▸ ht
    dsimp [radialPhaseSpeed]
    rw [radialVelocity_clamped_eq d R B t ⟨htI.1,htI.2.trans hr.2⟩]
  exact (hi.congr (Eventually.of_forall (fun n r hr => heq (c n) (H n) r hr))).congr_right
    (fun r hr => heq c₀ A r hr)

end DefocusingNLS

end OAI
