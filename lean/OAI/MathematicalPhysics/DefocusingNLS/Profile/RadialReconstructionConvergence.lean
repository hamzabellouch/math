import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexConvergence

namespace OAI

/-! C1 convergence of the genuine reconstructed inner profiles, including the origin. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_reconstruction_C1_convergence (R : ℝ) (hR : 0 ≤ R)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : ∀ n, c n ∈ Icc (599/100 : ℝ) 6)
    (hcT : Tendsto c atTop (𝓝 c₀))
    (H : ℕ → ℝ → ℝ) (A D : ℝ → ℝ) (hH : ∀ n, Differentiable ℝ (H n))
    (hA : Continuous A) (hD : Continuous D)
    (hHI : ∀ n r, r ∈ Icc 0 R → H n r ∈ Icc (999/1000 : ℝ) 1)
    (hTA : TendstoUniformlyOn H A atTop (Icc 0 R))
    (hTD : TendstoUniformlyOn (fun n => deriv (H n)) D atTop (Icc 0 R)) :
    TendstoUniformlyOn
      (fun n => radialPolar (H n) (radialPhase (c n) (radialClampedAmplitude R (H n))))
      (radialPolar A (radialPhase c₀ (radialClampedAmplitude R A))) atTop (Icc 0 R) ∧
    TendstoUniformlyOn
      (fun n => deriv (radialPolar (H n) (radialPhase (c n) (radialClampedAmplitude R (H n)))))
      (radialPolarSlope A D (radialPhaseSpeed c₀ A)
        (radialPhase c₀ (radialClampedAmplitude R A))) atTop (Icc 0 R) := by
  have hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1 := by
    intro r hr
    exact ⟨ge_of_tendsto' (hTA.tendsto_at hr) (fun n => (hHI n r hr).1),
      le_of_tendsto' (hTA.tendsto_at hr) (fun n => (hHI n r hr).2)⟩
  have hAz : ∀ r, radialClampedAmplitude R A r ≠ 0 := fun r =>
    ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI _ (radialClamp_mem R r hR)).1)
  have hHc : ∀ n, Continuous (H n) := fun n => (hH n).continuous
  have hHnz (n : ℕ) : ∀ r, radialClampedAmplitude R (H n) r ≠ 0 := fun r =>
    ne_of_gt (lt_of_lt_of_le (by norm_num) (hHI n _ (radialClamp_mem R r hR)).1)
  have hφ := radial_phase_clamped_uniform R hR c c₀ hc hcT H A hHc hA hHI hAI hTA
  have hv := radial_phase_speed_uniform R c c₀ hc hcT H A hHc hA hHI hAI hTA
  have hψ : Continuous (radialPhase c₀ (radialClampedAmplitude R A)) :=
    (radialPhase_differentiable c₀ _ (radialClampedAmplitude_continuous R A hA) hAz).continuous
  have hw := radial_phase_speed_continuousOn c₀ R A hR hA
    (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI r hr).1))
  obtain ⟨hQ,hJ⟩ := radial_polar_jet_uniform R H (fun n => deriv (H n))
    (fun n => radialPhaseSpeed (c n) (H n))
    (fun n => radialPhase (c n) (radialClampedAmplitude R (H n)))
    A D (radialPhaseSpeed c₀ A) (radialPhase c₀ (radialClampedAmplitude R A))
    hA hD hw hψ hTA hTD hv hφ
  refine ⟨hQ,hJ.congr (Eventually.of_forall (fun n r hr => ?_))⟩
  have hPh := radialPhase_differentiable (c n) _
    (radialClampedAmplitude_continuous R (H n) (hHc n)) (hHnz n)
  have hDPh := (radialPhase_hasDerivAt (c n) _
    (radialClampedAmplitude_continuous R (H n) (hHc n)) (hHnz n) r).deriv
  rw [radialVelocity_clamped_eq (c n) R (H n) r hr] at hDPh
  have hd := (radialPolar_hasDerivAt (H n) _ (hH n) hPh r).deriv
  rw [hd,hDPh]
  rfl

end DefocusingNLS

end OAI
