import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalFrame

namespace OAI

/-! Explicit size bounds for the initial physical frame. -/

namespace DefocusingNLS

private theorem pair_bound (A B : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (K : ℝ) (hK : 0 ≤ K)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K) : ‖A.prodMap B‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro z
  change max ‖A z.1‖ ‖B z.2‖ ≤ K*‖z‖
  apply max_le
  · exact (A.le_opNorm z.1).trans ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le z) hK))
  · exact (B.le_opNorm z.2).trans ((mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le z) hK))

theorem spectralRemoteInitialFrame_inverse_eq (c : Fin 2 → ℝ)
    (hc : ∀ i, |c i| ≤ 1/32) :
    Ring.inverse (spectralRemoteInitialFrame c) = spectralRemoteInitialFrameInverse c := by
  have hp := (homogeneousSpectralLocalizationRemoteFrame_bounds 1 (c 0) (by norm_num) (hc 0)).1
  have hm := (homogeneousSpectralLocalizationRemoteFrame_bounds (-1) (c 1) (by norm_num) (hc 1)).1
  have he : spectralRemoteInitialFrame c*spectralRemoteInitialFrameInverse c = 1 := by
    apply ContinuousLinearMap.ext
    intro z
    exact Prod.ext (spectralTwoColumns_apply_inverse _ _ z.1 hp)
      (spectralTwoColumns_apply_inverse _ _ z.2 hm)
  have hh := (Ring.inverse_mul_eq_iff_eq_mul (spectralRemoteInitialFrame c) 1
    (spectralRemoteInitialFrameInverse c) (spectralRemoteInitialFrame_unit c hc)).mpr he.symm
  simpa only [mul_one] using hh

theorem spectralRemoteInitialFrame_bounds (c : Fin 2 → ℝ)
    (hc : ∀ i, |c i| ≤ 1/32) :
    ‖spectralRemoteInitialFrame c‖ ≤ 2 ∧
      ‖Ring.inverse (spectralRemoteInitialFrame c)‖ ≤ 8 := by
  have hp := (homogeneousSpectralLocalizationRemoteFrame_bounds 1 (c 0) (by norm_num) (hc 0)).2
  have hm := (homogeneousSpectralLocalizationRemoteFrame_bounds (-1) (c 1) (by norm_num) (hc 1)).2
  constructor
  · exact pair_bound _ _ 2 (by norm_num) hp.1 hm.1
  · rw [spectralRemoteInitialFrame_inverse_eq c hc]
    exact pair_bound _ _ 8 (by norm_num) hp.2 hm.2

end DefocusingNLS

end OAI
