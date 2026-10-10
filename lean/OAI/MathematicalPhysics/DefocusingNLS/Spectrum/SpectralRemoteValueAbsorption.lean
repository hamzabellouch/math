import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFrameTrace

namespace OAI

/-! A small incoming part controls the full remote state by its physical values. -/

namespace DefocusingNLS

theorem spectralRemote_value_norm_le (z : SpectralRemoteSpace) :
    ‖spectralPhysicalValueMap z‖ ≤ ‖z‖ := by
  change max ‖z.1.1‖ ‖z.2.1‖ ≤ max ‖z.1‖ ‖z.2‖
  exact max_le ((norm_fst_le z.1).trans (le_max_left _ _))
    ((norm_fst_le z.2).trans (le_max_right _ _))

theorem spectralRemote_velocity_norm_le (z : SpectralRemoteSpace) :
    ‖spectralPhysicalDerivativeMap z‖ ≤ ‖z‖ := by
  change max ‖z.1.2‖ ‖z.2.2‖ ≤ max ‖z.1‖ ‖z.2‖
  exact max_le ((norm_snd_le z.1).trans (le_max_left _ _))
    ((norm_snd_le z.2).trans (le_max_right _ _))

theorem spectralRemote_norm_trace (z : SpectralRemoteSpace) :
    ‖z‖ = max ‖spectralPhysicalValueMap z‖ ‖spectralPhysicalDerivativeMap z‖ := by
  change max (max ‖z.1.1‖ ‖z.1.2‖) (max ‖z.2.1‖ ‖z.2.2‖) = _
  exact max_max_max_comm _ _ _ _

theorem spectralRemote_small_incoming (c : Fin 2 → ℝ) (T : SpectralRemoteOperator)
    (z : SpectralRemoteSpace) (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps ≤ 1/6)
    (hT : ‖T-1‖ ≤ eps) (hin : ‖spectralPhysicalDerivativeMap z‖ ≤ eps*‖z‖) :
    ‖z‖ ≤ 2*‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖ ∧
    ‖spectralPhysicalDerivativeMap (T z)‖ ≤ 2*eps*‖z‖ := by
  have herr : ‖T z-z‖ ≤ eps*‖z‖ := by
    calc
      _ = ‖(T-1) z‖ := by rw [sub_apply]; rfl
      _ ≤ ‖T-1‖*‖z‖ := (T-1).le_opNorm z
      _ ≤ _ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)
  have hI : ‖spectralPhysicalDerivativeMap (T z)‖ ≤ 2*eps*‖z‖ := by
    calc
      _ = ‖spectralPhysicalDerivativeMap (T z-z)+spectralPhysicalDerivativeMap z‖ := by rw [map_sub,sub_add_cancel]
      _ ≤ ‖spectralPhysicalDerivativeMap (T z-z)‖+‖spectralPhysicalDerivativeMap z‖ := norm_add_le _ _
      _ ≤ eps*‖z‖+eps*‖z‖ := add_le_add ((spectralRemote_velocity_norm_le _).trans herr) hin
      _ = _ := by ring
  have hv : ‖spectralPhysicalValueMap z-spectralPhysicalValueMap (T z)‖ ≤ eps*‖z‖ := by
    rw [norm_sub_rev,← map_sub]
    exact (spectralRemote_value_norm_le _).trans herr
  have hW : ‖spectralPhysicalValueMap (T z)‖ ≤
      ‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖+2*eps*‖z‖ := by
    calc
      _ = ‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))-
          spectralPhysicalDerivativeMap (T z)‖ := by
        rw [spectralRemoteInitialFrame_value,add_sub_cancel_right]
      _ ≤ ‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖+
          ‖spectralPhysicalDerivativeMap (T z)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add_right hI _
  have hV : ‖spectralPhysicalValueMap z‖ ≤
      ‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖+3*eps*‖z‖ := by
    have hh : ‖spectralPhysicalValueMap z‖ ≤
        ‖spectralPhysicalValueMap z-spectralPhysicalValueMap (T z)‖+‖spectralPhysicalValueMap (T z)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (spectralPhysicalValueMap z-spectralPhysicalValueMap (T z)) (spectralPhysicalValueMap (T z))
    nlinarith
  have hz : ‖z‖ ≤ ‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖+3*eps*‖z‖ := by
    have hrest : ‖spectralPhysicalDerivativeMap z‖ ≤
        ‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖+3*eps*‖z‖ := by
      nlinarith [norm_nonneg (spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))),
        norm_nonneg z]
    exact (spectralRemote_norm_trace z).le.trans (max_le hV hrest)
  refine ⟨?_,hI⟩
  nlinarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg z)]

theorem spectralRemote_small_incoming_velocity (c : Fin 2 → ℝ) (T : SpectralRemoteOperator)
    (z : SpectralRemoteSpace) (eps : ℝ) (heps : 0 ≤ eps) (hsmall : eps ≤ 1/6)
    (hc : ∀ i, |c i| ≤ 1/32) (hT : ‖T-1‖ ≤ eps)
    (hin : ‖spectralPhysicalDerivativeMap z‖ ≤ eps*‖z‖) :
    ‖spectralPhysicalDerivativeMap (spectralRemoteInitialFrame c (T z))-
      homogeneousDiagonal (homogeneousSpectralLocalizationRemoteRoot 1 1 (c 0))
        (homogeneousSpectralLocalizationRemoteRoot (-1) 1 (c 1))
          (spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z)))‖ ≤
      8*eps*‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖ := by
  obtain ⟨hz,hI⟩ := spectralRemote_small_incoming c T z eps heps hsmall hT hin
  calc
    _ ≤ 2*‖spectralPhysicalDerivativeMap (T z)‖ := spectralRemoteInitialFrame_velocity_bound c (T z) hc
    _ ≤ 2*(2*eps*‖z‖) := mul_le_mul_of_nonneg_left hI (by norm_num)
    _ ≤ 8*eps*‖spectralPhysicalValueMap (spectralRemoteInitialFrame c (T z))‖ := by nlinarith

end DefocusingNLS

end OAI
