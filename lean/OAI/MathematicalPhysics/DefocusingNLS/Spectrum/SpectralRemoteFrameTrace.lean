import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFrameBounds

namespace OAI

/-! Value and velocity traces in the physical leading frame. -/

namespace DefocusingNLS

theorem spectralRemoteInitialFrame_value (c : Fin 2 → ℝ) (z : SpectralRemoteSpace) :
    spectralPhysicalValueMap (spectralRemoteInitialFrame c z) =
      spectralPhysicalValueMap z+spectralPhysicalDerivativeMap z := by
  apply Prod.ext <;> simp [spectralPhysicalValueMap,spectralPhysicalDerivativeMap,
    spectralRemoteInitialFrame,spectralRemoteInitialFramePart,spectralTwoColumns_apply]

theorem spectralRemoteInitialFrame_velocity_error (c : Fin 2 → ℝ) (z : SpectralRemoteSpace) :
    spectralPhysicalDerivativeMap (spectralRemoteInitialFrame c z)-
      homogeneousDiagonal (homogeneousSpectralLocalizationRemoteRoot 1 1 (c 0))
        (homogeneousSpectralLocalizationRemoteRoot (-1) 1 (c 1))
          (spectralPhysicalValueMap (spectralRemoteInitialFrame c z)) =
      homogeneousDiagonal
        (homogeneousSpectralLocalizationRemoteRoot 1 (-1) (c 0)-homogeneousSpectralLocalizationRemoteRoot 1 1 (c 0))
        (homogeneousSpectralLocalizationRemoteRoot (-1) (-1) (c 1)-homogeneousSpectralLocalizationRemoteRoot (-1) 1 (c 1))
          (spectralPhysicalDerivativeMap z) := by
  apply Prod.ext <;>
    simp [spectralPhysicalValueMap,spectralPhysicalDerivativeMap,spectralRemoteInitialFrame,
      spectralRemoteInitialFramePart,spectralTwoColumns_apply,homogeneousDiagonal_apply] <;> ring

theorem spectralRemoteInitialFrame_velocity_bound (c : Fin 2 → ℝ) (z : SpectralRemoteSpace)
    (hc : ∀ i, |c i| ≤ 1/32) :
    ‖spectralPhysicalDerivativeMap (spectralRemoteInitialFrame c z)-
      homogeneousDiagonal (homogeneousSpectralLocalizationRemoteRoot 1 1 (c 0))
        (homogeneousSpectralLocalizationRemoteRoot (-1) 1 (c 1))
          (spectralPhysicalValueMap (spectralRemoteInitialFrame c z))‖ ≤
      2*‖spectralPhysicalDerivativeMap z‖ := by
  rw [spectralRemoteInitialFrame_velocity_error,homogeneousDiagonal_apply]
  have hp : ‖homogeneousSpectralLocalizationRemoteRoot 1 (-1) (c 0)-
      homogeneousSpectralLocalizationRemoteRoot 1 1 (c 0)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (add_le_add
      (homogeneousSpectralLocalizationRemoteRoot_norm 1 (-1) (c 0) (by norm_num) (by norm_num) (hc 0))
      (homogeneousSpectralLocalizationRemoteRoot_norm 1 1 (c 0) (by norm_num) (by norm_num) (hc 0)) |>.trans_eq (by norm_num))
  have hm : ‖homogeneousSpectralLocalizationRemoteRoot (-1) (-1) (c 1)-
      homogeneousSpectralLocalizationRemoteRoot (-1) 1 (c 1)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (add_le_add
      (homogeneousSpectralLocalizationRemoteRoot_norm (-1) (-1) (c 1) (by norm_num) (by norm_num) (hc 1))
      (homogeneousSpectralLocalizationRemoteRoot_norm (-1) 1 (c 1) (by norm_num) (by norm_num) (hc 1)) |>.trans_eq (by norm_num))
  rw [Prod.norm_def]
  apply max_le
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le _) (by norm_num))
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hm (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le _) (by norm_num))

end DefocusingNLS

end OAI
