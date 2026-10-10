import OAI.Analysis.KadisonKastler.FourierIntegralL2

namespace OAI

/-! # Fourier uniqueness for integrable vector functions

The distribution embedding is injective. Fubini identifies its Fourier
transform with the ordinary integral Fourier transform, so a vanishing
integral transform forces the original function to vanish almost everywhere.
-/

namespace KadisonKastler

open MeasureTheory SchwartzMap FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

theorem ae_zero_of_integrable_fourier_zero {f : ℝ → H} (hf : Integrable f)
    (hz : ∀ t : ℝ, 𝓕 f t = 0) : f =ᵐ[volume] 0 := by
  let hm : MemLp f 1 := memLp_one_iff_integrable.mpr hf
  let F : Lp H 1 (volume : Measure ℝ) := hm.toLp f
  have hF : 𝓕 (Lp.toTemperedDistribution F) = 0 := by
    ext g
    rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
    calc
      (∫ s, (𝓕 g) s • F s) = ∫ s, (𝓕 g) s • f s := by
        apply integral_congr_ae
        filter_upwards [hm.coeFn_toLp] with s hs
        rw [show F s = f s from hs]
      _ = ∫ s, g s • 𝓕 f s := by
        simpa only [SchwartzMap.fourier_coe, Real.fourier_eq,
          VectorFourier.fourierIntegral, LinearMap.flip_apply, innerₗ_apply_apply,
          real_inner_comm] using!
          (VectorFourier.integral_fourierIntegral_smul_eq_flip
            (μ := volume) (ν := volume) (L := innerₗ ℝ)
            Real.continuous_fourierChar (by fun_prop) g.integrable hf)
      _ = 0 := by simp [hz]
  have hdist : Lp.toTemperedDistribution F = 0 := by
    have h := congrArg (fun d : 𝓢'(ℝ, H) => 𝓕⁻ d) hF
    simpa using h
  have hzero : F = 0 := by
    apply (LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := H) (μ := volume) (p := 1)))
    change Lp.toTemperedDistribution F = Lp.toTemperedDistribution 0
    have hz0 : Lp.toTemperedDistribution (0 : Lp H 1 (volume : Measure ℝ)) = 0 :=
      (Lp.toTemperedDistributionCLM H volume 1).map_zero
    exact hdist.trans hz0.symm
  have hae : F =ᵐ[volume] 0 := (Lp.eq_zero_iff_ae_eq_zero).mp hzero
  filter_upwards [hae, hm.coeFn_toLp] with s hs hs'
  exact hs'.symm.trans hs

end

end KadisonKastler

end OAI
